{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Var (..),
        SysVar (..),
        VarField,
        Arithmetic,
        Constraint,
        -- variable getters
        acInput,
        getAllVars,
        -- input mapping
        hlmap,
        -- evaluation functions
        witnessGenerator,
        eval,
        eval1,
        exec,
        exec1,
        apply,
        indexW
    ) where

import           Control.DeepSeq                                       (NFData)
import           Control.Monad.State                                   (State, modify, runState)
import           Data.Aeson
import           Data.Binary                                           (Binary)
import           Data.ByteString                                       (ByteString)
import           Data.Foldable                                         (fold, toList)
import           Data.Functor.Rep
import           Data.Map.Strict                                       hiding (drop, foldl, foldr, map, null, splitAt,
                                                                        take, toList)
import           Data.Maybe                                            (fromMaybe)
import           Data.Semialign                                        (unzipDefault)
import           Data.Semigroup.Generic                                (GenericSemigroupMonoid (..))
import           GHC.Generics                                          (Generic, Par1 (..), U1 (..), (:*:) (..))
import           Optics
import           Prelude                                               hiding (Num (..), drop, length, product, splitAt,
                                                                        sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                       (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate          (Poly, evalMonomial, evalPolynomial, mapVars,
                                                                        var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MerkleHash
import           ZkFold.Symbolic.MonadCircuit
import ZkFold.Symbolic.Data.Class (SymbolicData(..))
import Data.Proxy (Proxy)

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c i = Poly c (SysVar i) Natural

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a i o = ArithmeticCircuit
    {
        acSystem  :: Map ByteString (Constraint a i),
        -- ^ The system of polynomial constraints
        acRange   :: Map (SysVar i) a,
        -- ^ The range constraints [0, a] for the selected variables
        acWitness :: Map ByteString (i a -> Map ByteString a -> a),
        -- ^ The witness generation functions
        acOutput  :: o (Var a i)
        -- ^ The output variables
    } deriving (Generic)

deriving via (GenericSemigroupMonoid (ArithmeticCircuit a i o))
  instance (Ord (Rep i), o ~ U1) => Semigroup (ArithmeticCircuit a i o)

deriving via (GenericSemigroupMonoid (ArithmeticCircuit a i o))
  instance (Ord (Rep i), o ~ U1) => Monoid (ArithmeticCircuit a i o)

instance (NFData a, NFData (o (Var a i)), NFData (Rep i))
    => NFData (ArithmeticCircuit a i o)

-- | Variables are SHA256 digests (32 bytes)
type VarField = Zp (2 ^ (32 * 8))

data SysVar i
  = InVar (Rep i)
  | NewVar ByteString
  deriving Generic
deriving anyclass instance FromJSON (Rep i) => FromJSON (SysVar i)
deriving anyclass instance FromJSON (Rep i) => FromJSONKey (SysVar i)
deriving anyclass instance ToJSON (Rep i) => ToJSONKey (SysVar i)
deriving anyclass instance ToJSON (Rep i) => ToJSON (SysVar i)
deriving stock instance Show (Rep i) => Show (SysVar i)
deriving stock instance Eq (Rep i) => Eq (SysVar i)
deriving stock instance Ord (Rep i) => Ord (SysVar i)
deriving instance NFData (Rep i) => NFData (SysVar i)

imapSysVar ::
  (Representable i, Representable j) =>
  (forall x. j x -> i x) -> SysVar i -> SysVar j
imapSysVar f (InVar r)  = index (f (tabulate InVar)) r
imapSysVar _ (NewVar b) = NewVar b

data Var a i
  = SysVar (SysVar i)
  | ConstVar a
  deriving Generic
deriving anyclass instance (FromJSON (Rep i), FromJSON a) => FromJSON (Var a i)
deriving anyclass instance (FromJSON (Rep i), FromJSON a) => FromJSONKey (Var a i)
deriving anyclass instance (ToJSON (Rep i), ToJSON a) => ToJSONKey (Var a i)
deriving anyclass instance (ToJSON (Rep i), ToJSON a) => ToJSON (Var a i)
deriving stock instance (Show (Rep i), Show a) => Show (Var a i)
deriving stock instance (Eq (Rep i), Eq a) => Eq (Var a i)
deriving stock instance (Ord (Rep i), Ord a) => Ord (Var a i)
deriving instance (NFData (Rep i), NFData a) => NFData (Var a i)
instance FromConstant a (Var a i) where
    fromConstant = ConstVar

imapVar ::
  (Representable i, Representable j) =>
  (forall x. j x -> i x) -> Var a i -> Var a j
imapVar f (SysVar s)   = SysVar (imapSysVar f s)
imapVar _ (ConstVar c) = ConstVar c

---------------------------------- Variables -----------------------------------

acInput :: forall f s a l c. 
  ( s ~ Support f
    , c ~ ArithmeticCircuit a l
    , SymbolicData s
    , Layout s ~ l
    , Context s ~ c
    , Support s ~ Proxy c
    , Representable l
    , Ord (Rep l)
  ) => Support f
acInput = restore @(Support f) $ const inputC
    where
        inputC = mempty { acOutput = acInput' } 
        acInput' = fmapRep (SysVar . InVar) (tabulate id ) 

getAllVars :: forall a i o. (Representable i, Foldable i) => ArithmeticCircuit a i o -> [SysVar i]
getAllVars ac = toList acInput0 ++ map NewVar (keys $ acWitness ac) where
  acInput0 :: i (SysVar i)
  acInput0 = fmapRep InVar (tabulate @i id)

indexW :: Representable i => ArithmeticCircuit a i o -> i a -> Var a i -> a
indexW circuit inputs = \case
  SysVar (InVar inV) -> index inputs inV
  SysVar (NewVar newV) -> fromMaybe
    (error ("no such NewVar: " <> show newV))
    (witnessGenerator circuit inputs !? newV)
  ConstVar cV -> cV

-------------------------------- "HProfunctor" ---------------------------------

hlmap ::
  (Representable i, Representable j, Ord (Rep j), Functor o) =>
  (forall x . j x -> i x) -> ArithmeticCircuit a i o -> ArithmeticCircuit a j o
hlmap f (ArithmeticCircuit s r w o) = ArithmeticCircuit
  { acSystem = mapVars (imapSysVar f) <$> s
  , acRange = mapKeys (imapSysVar f) r
  , acWitness = (\g j p -> g (f j) p) <$> w
  , acOutput = imapVar f <$> o
  }

--------------------------- Symbolic compiler context --------------------------

crown :: ArithmeticCircuit a i g -> f (Var a i) -> ArithmeticCircuit a i f
crown = flip (set #acOutput)

behead :: ArithmeticCircuit a i f -> (ArithmeticCircuit a i U1, f (Var a i))
behead = liftA2 (,) (set #acOutput U1) acOutput

instance HFunctor (ArithmeticCircuit a i) where
    hmap = over #acOutput

instance Ord (Rep i) => HApplicative (ArithmeticCircuit a i) where
    hpure = crown mempty
    hliftA2 f (behead -> (c, o)) (behead -> (d, p)) = crown (c <> d) (f o p)

instance Ord (Rep i) => Package (ArithmeticCircuit a i) where
    unpackWith f (behead -> (c, o)) = crown c <$> f o
    packWith f (unzipDefault . fmap behead -> (cs, os)) = crown (fold cs) (f os)

instance
  (Arithmetic a, Binary a, Representable i, Binary (Rep i), Ord (Rep i)) =>
  Symbolic (ArithmeticCircuit a i) where
    type BaseField (ArithmeticCircuit a i) = a
    symbolicF (behead -> (c, o)) _ f = uncurry (set #acOutput) (runState (f o) c)

----------------------------- MonadCircuit instance ----------------------------

instance
  ( Arithmetic a, Binary a, Representable i, Binary (Rep i), Ord (Rep i)
  , o ~ U1) => MonadCircuit (Var a i) a (State (ArithmeticCircuit a i o)) where

    unconstrained witness = do
      let v = toVar @a witness
      -- TODO: forbid reassignment of variables
      zoom #acWitness . modify $ insert v $ \i w -> witness $ \case
        SysVar (InVar inV) -> index i inV
        SysVar (NewVar newV) -> w ! newV
        ConstVar cV -> fromConstant cV
      return (SysVar (NewVar v))

    constraint p =
      let
        evalConstVar = \case
          SysVar sysV -> var sysV
          ConstVar cV -> fromConstant cV
      in
        zoom #acSystem . modify $ insert (toVar @a p) (p evalConstVar)

    rangeConstraint (SysVar v) upperBound =
      zoom #acRange . modify $ insert v upperBound
    -- FIXME range-constrain other variable types
    rangeConstraint _ _ = error "Cannot range-constrain this variable"

-- | Generates new variable index given a witness for it.
--
-- It is a root hash (sha256) of a Merkle tree which is obtained from witness:
--
-- 1. Due to parametricity, the only operations inside witness are
--    operations from 'WitnessField' interface;
--
-- 2. Thus witness can be viewed as an AST of a 'WitnessField' "language" where:
--
--     * leafs are 'fromConstant' calls and variables;
--     * nodes are algebraic operations;
--     * root is the witness value for new variable.
--
-- 3. To inspect this AST, we instantiate witness with a special inspector type
--    whose 'WitnessField' instances perform inspection.
--
-- 4. Inspector type used here, 'MerkleHash', treats AST as a Merkle tree and
--    performs the calculation of hashes for it.
--
-- 5. Thus the result of running the witness with 'MerkleHash' as a
--    'WitnessField' is a root hash of a Merkle tree for a witness.
toVar ::
  forall a i. (Finite a, Binary a, Binary (Rep i)) =>
  Witness (Var a i) a -> ByteString
toVar witness = runHash @(Just (Order a)) $ witness $ \case
  SysVar (InVar inV) -> merkleHash inV
  SysVar (NewVar newV) -> M newV
  ConstVar cV -> fromConstant cV

----------------------------- Evaluation functions -----------------------------

witnessGenerator :: ArithmeticCircuit a i o -> i a -> Map ByteString a
witnessGenerator circuit inputs =
  let result = fmap (\k -> k inputs result) (acWitness circuit)
  in result

-- | Evaluates the arithmetic circuit with one output using the supplied input map.
eval1 :: Representable i => ArithmeticCircuit a i Par1 -> i a -> a
eval1 ctx i = unPar1 (eval ctx i)

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: (Representable i, Functor o) => ArithmeticCircuit a i o -> i a -> o a
eval ctx i = indexW ctx i <$> acOutput ctx

-- | Evaluates the arithmetic circuit with no inputs and one output.
exec1 :: ArithmeticCircuit a U1 Par1 -> a
exec1 ac = eval1 ac U1

-- | Evaluates the arithmetic circuit with no inputs.
exec :: Functor o => ArithmeticCircuit a U1 o -> o a
exec ac = eval ac U1

-- | Applies the values of the first couple of inputs to the arithmetic circuit.
apply ::
  (Eq a, Field a, Ord (Rep j), Representable i) =>
  i a -> ArithmeticCircuit a (i :*: j) U1 -> ArithmeticCircuit a j U1
apply xs ac = ac
  { acSystem = fmap (evalPolynomial evalMonomial varF) (acSystem ac)
  , acRange = mapKeys' (acRange ac)
  , acWitness = fmap witF (acWitness ac)
  , acOutput = U1
  }
  where
    varF (InVar (Left v))  = fromConstant (index xs v)
    varF (InVar (Right v)) = var (InVar v)
    varF (NewVar v)        = var (NewVar v)
    witF f j = f (xs :*: j)

    mapKeys' :: Ord (SysVar j) =>  Map (SysVar (i :*: j)) a ->  Map (SysVar j) a
    mapKeys' m = fromList $
                  foldrWithKey (\k x ms -> case k of
                    NewVar v        -> (NewVar v, x) : ms
                    InVar (Right v) -> (InVar v, x) : ms
                    _               -> ms) [] m

-- TODO: Add proper symbolic application functions

-- applySymOne :: ArithmeticCircuit a -> State (ArithmeticCircuit a) ()
-- applySymOne x = modify (\(f :: ArithmeticCircuit a) ->
--     let ins = acInput f
--     in f
--     {
--         acInput = tail ins,
--         acWitness = acWitness f . (singleton (head ins) (eval x empty)  `union`)
--     })

-- applySym :: [ArithmeticCircuit a] -> State (ArithmeticCircuit a) ()
-- applySym = foldr ((>>) . applySymOne) (return ())

-- applySymArgs :: ArithmeticCircuit a -> [ArithmeticCircuit a] -> ArithmeticCircuit a
-- applySymArgs x xs = execState (applySym xs) x
