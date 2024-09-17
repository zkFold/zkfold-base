{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Var (..),
        VarField,
        Arithmetic,
        Constraint,
        -- variable getters
        acInput,
        getAllVars,
        -- evaluation functions
        witnessGenerator,
        eval,
        eval1,
        exec,
        exec1,
        apply,
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
import           Data.Semialign                                        (unzipDefault)
import           GHC.Generics                                          (Generic, Par1 (..), U1 (..), (:*:) (..))
import           Optics
import           Prelude                                               hiding (Num (..), drop, length, product, splitAt,
                                                                        sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                       (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate          (Poly, evalMonomial, evalPolynomial, var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MerkleHash
import           ZkFold.Symbolic.MonadCircuit

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c i = Poly c (Var i) Natural

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a i o = ArithmeticCircuit
    {
        acSystem  :: Map ByteString (Constraint a i),
        -- ^ The system of polynomial constraints
        acRange   :: Map ByteString a,
        -- ^ The range constraints [0, a] for the selected variables
        acWitness :: Map ByteString (i a -> Map ByteString a -> a),
        -- ^ The witness generation functions
        acOutput  :: o (Var i)
        -- ^ The output variables
    } deriving (Generic)
deriving instance (NFData a, NFData (o (Var i)), NFData (Rep i))
    => NFData (ArithmeticCircuit a i o)

-- | Variables are SHA256 digests (32 bytes)
type VarField = Zp (2 ^ (32 * 8))

data Var i
  = InVar (Rep i)
  | NewVar ByteString
  deriving Generic
deriving anyclass instance FromJSON (Rep i) => FromJSON (Var i)
deriving anyclass instance FromJSON (Rep i) => FromJSONKey (Var i)
deriving anyclass instance ToJSON (Rep i) => ToJSONKey (Var i)
deriving anyclass instance ToJSON (Rep i) => ToJSON (Var i)
deriving stock instance Show (Rep i) => Show (Var i)
deriving stock instance Eq (Rep i) => Eq (Var i)
deriving stock instance Ord (Rep i) => Ord (Var i)
deriving instance NFData (Rep i) => NFData (Var i)

---------------------------------- Variables -----------------------------------

acInput :: Representable i => i (Var i)
acInput = tabulate InVar

getAllVars :: (Representable i, Foldable i) => ArithmeticCircuit a i o -> [Var i]
getAllVars ac = toList acInput ++ map NewVar (keys $ acWitness ac)

--------------------------- Symbolic compiler context --------------------------

crown :: ArithmeticCircuit a i g -> f (Var i) -> ArithmeticCircuit a i f
crown = flip (set #acOutput)

behead :: ArithmeticCircuit a i f -> (ArithmeticCircuit a i U1, f (Var i))
behead = liftA2 (,) (set #acOutput U1) acOutput

instance HFunctor (ArithmeticCircuit a i) where
    hmap = over #acOutput

instance HApplicative (ArithmeticCircuit a i) where
    hpure = crown mempty
    hliftA2 f (behead -> (c, o)) (behead -> (d, p)) = crown (c <> d) (f o p)

instance Package (ArithmeticCircuit a i) where
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
  , o ~ U1) => MonadCircuit (Var i) a (State (ArithmeticCircuit a i o)) where

    newRanged upperBound witness = do
      i <- unconstrained witness
      zoom #acRange . modify $ insert i upperBound
      return (NewVar i)

    newConstrained new witness = do
      i <- unconstrained witness
      constraint (`new` NewVar i)
      return (NewVar i)

    constraint p = zoom #acSystem . modify $ insert (toVar @a p) (p var)

unconstrained ::
  forall a i. (Arithmetic a, Binary a, Representable i, Binary (Rep i)) =>
  Witness (Var i) a -> State (ArithmeticCircuit a i U1) ByteString
unconstrained witness = do
  let v = toVar @a witness
  -- TODO: forbid reassignment of variables
  zoom #acWitness . modify $ insert v $ \i w -> witness $ \case
    InVar inV -> index i inV
    NewVar newV -> w ! newV
  return v

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
  Witness (Var i) a -> ByteString
toVar witness = runHash @(Just (Order a)) $ witness $ \case
  InVar inV -> merkleHash inV
  NewVar newV -> M newV

-------------------------------- Circuit monoid --------------------------------

instance o ~ U1 => Semigroup (ArithmeticCircuit a i o) where
    c1 <> c2 =
        ArithmeticCircuit
           {   acSystem   = acSystem c1 `union` acSystem c2
           ,   acRange    = acRange c1 `union` acRange c2
           ,   acWitness  = acWitness c1 `union` acWitness c2
           ,   acOutput   = U1
           }

instance o ~ U1 => Monoid (ArithmeticCircuit a i o) where
    mempty =
        ArithmeticCircuit
           {
               acSystem   = empty,
               acRange    = empty,
               acWitness  = empty,
               acOutput   = U1
           }

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
eval ctx i = acOutput ctx <&> \case
    NewVar k -> witnessGenerator ctx i ! k
    InVar j -> index i j

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
  , acWitness = fmap witF (acWitness ac)
  , acOutput = U1
  }
  where
    varF (InVar (Left v))  = fromConstant (index xs v)
    varF (InVar (Right v)) = var (InVar v)
    varF (NewVar v)        = var (NewVar v)
    witF f j = f (xs :*: j)

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
