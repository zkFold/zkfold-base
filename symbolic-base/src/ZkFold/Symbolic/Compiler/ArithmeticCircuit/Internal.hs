{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Var (..),
        SysVar (..),
        WitVar (..),
        VarField,
        Arithmetic,
        Constraint,
        -- variable getters and setters
        acInput,
        getAllVars,
        crown,
        -- input mapping
        hlmap,
        hpmap,
        -- evaluation functions
        witnessGenerator,
        eval,
        eval1,
        exec,
        exec1,
        apply,
        indexW,
        witToVar
    ) where

import           Control.DeepSeq                                              (NFData)
import           Control.Monad.State                                          (State, modify, runState)
import           Data.Binary                                                  (Binary)
import           Data.ByteString                                              (ByteString)
import           Data.Foldable                                                (fold, toList)
import           Data.Functor.Rep
import           Data.Map.Monoidal                                            (MonoidalMap, insertWith)
import           Data.Map.Strict                                              hiding (drop, foldl, foldr, insertWith,
                                                                               map, null, splitAt, take, toList)
import           Data.Maybe                                                   (catMaybes, fromMaybe)
import           Data.Semialign                                               (unzipDefault)
import           Data.Semigroup.Generic                                       (GenericSemigroupMonoid (..))
import qualified Data.Set                                                     as S
import           GHC.Generics                                                 (Generic, Par1 (..), U1 (..), (:*:) (..))
import           Optics                                                       hiding (at)
import           Prelude                                                      hiding (Num (..), drop, length, product,
                                                                               splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                              (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate                 (Poly, evalMonomial, evalPolynomial,
                                                                               mapVars, var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MerkleHash
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Var
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.WitnessEstimation
import           ZkFold.Symbolic.MonadCircuit

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c i = Poly c (SysVar i) Natural

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a p i o = ArithmeticCircuit
    {
        acSystem  :: Map ByteString (Constraint a i),
        -- ^ The system of polynomial constraints
        acRange   :: MonoidalMap a (S.Set (SysVar i)),
        -- ^ The range constraints [0, a] for the selected variables
        acWitness :: Map ByteString (WitnessF a (WitVar p i)),
        -- ^ The witness generation functions
        acOutput  :: o (Var a i)
        -- ^ The output variables
    } deriving (Generic)

deriving via (GenericSemigroupMonoid (ArithmeticCircuit a p i o))
  instance (Ord a, Ord (Rep i), o ~ U1) => Semigroup (ArithmeticCircuit a p i o)

deriving via (GenericSemigroupMonoid (ArithmeticCircuit a p i o))
  instance (Ord a, Ord (Rep i), o ~ U1) => Monoid (ArithmeticCircuit a p i o)

instance (NFData a, NFData (o (Var a i)), NFData (Rep i))
    => NFData (ArithmeticCircuit a p i o)

-- | Variables are SHA256 digests (32 bytes)
type VarField = Zp (2 ^ (32 * 8))

data WitVar p i
  = WExVar (Rep p)
  | WSysVar (SysVar i)

imapWitVar ::
  (Representable i, Representable j) =>
  (forall x. j x -> i x) -> WitVar p i -> WitVar p j
imapWitVar _ (WExVar r)  = WExVar r
imapWitVar f (WSysVar v) = WSysVar (imapSysVar f v)

pmapWitVar ::
  (Representable p, Representable q) =>
  (forall x. q x -> p x) -> WitVar p i -> WitVar q i
pmapWitVar f (WExVar r)  = index (f (tabulate WExVar)) r
pmapWitVar _ (WSysVar v) = WSysVar v

---------------------------------- Variables -----------------------------------

acInput :: (Representable i, Semiring a) => i (Var a i)
acInput = fmapRep (toVar . InVar) (tabulate id)

getAllVars :: forall a p i o. (Representable i, Foldable i) => ArithmeticCircuit a p i o -> [SysVar i]
getAllVars ac = toList acInput0 ++ map NewVar (keys $ acWitness ac) where
  acInput0 :: i (SysVar i)
  acInput0 = fmapRep InVar (tabulate @i id)

indexW ::
  (Arithmetic a, Representable p, Representable i) =>
  ArithmeticCircuit a p i o -> p a -> i a -> Var a i -> a
indexW circuit payload inputs = \case
  LinVar k (InVar inV) b -> (\t -> k * t + b) $ index inputs inV
  LinVar k (NewVar newV) b -> (\t -> k * t + b) $ fromMaybe
    (error ("no such NewVar: " <> show newV))
    (witnessGenerator circuit payload inputs !? newV)
  ConstVar cV -> cV

-------------------------------- "HProfunctor" ---------------------------------

hlmap ::
  (Representable i, Representable j, Ord (Rep j), Functor o) =>
  (forall x . j x -> i x) -> ArithmeticCircuit a p i o -> ArithmeticCircuit a p j o
hlmap f (ArithmeticCircuit s r w o) = ArithmeticCircuit
  { acSystem = mapVars (imapSysVar f) <$> s
  , acRange = S.map (imapSysVar f) <$> r
  , acWitness = fmap (imapWitVar f) <$> w
  , acOutput = imapVar f <$> o
  }

hpmap ::
  (Representable p, Representable q) => (forall x. q x -> p x) ->
  ArithmeticCircuit a p i o -> ArithmeticCircuit a q i o
hpmap f ac = ac { acWitness = fmap (pmapWitVar f) <$> acWitness ac }

--------------------------- Symbolic compiler context --------------------------

crown :: ArithmeticCircuit a p i g -> f (Var a i) -> ArithmeticCircuit a p i f
crown = flip (set #acOutput)

behead :: ArithmeticCircuit a p i f -> (ArithmeticCircuit a p i U1, f (Var a i))
behead = liftA2 (,) (set #acOutput U1) acOutput

instance HFunctor (ArithmeticCircuit a p i) where
    hmap = over #acOutput

instance (Ord (Rep i), Ord a) => HApplicative (ArithmeticCircuit a p i) where
    hpure = crown mempty
    hliftA2 f (behead -> (c, o)) (behead -> (d, p)) = crown (c <> d) (f o p)

instance (Ord (Rep i), Ord a) => Package (ArithmeticCircuit a p i) where
    unpackWith f (behead -> (c, o)) = crown c <$> f o
    packWith f (unzipDefault . fmap behead -> (cs, os)) = crown (fold cs) (f os)

instance
  (Arithmetic a, Binary a, Binary (Rep p), Binary (Rep i), Ord (Rep i), NFData (Rep i)) =>
  Symbolic (ArithmeticCircuit a p i) where
    type BaseField (ArithmeticCircuit a p i) = a
    type WitnessField (ArithmeticCircuit a p i) = WitnessF a (WitVar p i)
    witnessF (behead -> (c, o)) = o <&> \case
      LinVar k (NewVar nv) b -> fromConstant k * acWitness c ! nv + fromConstant b
      v -> at v
    fromCircuitF (behead -> (c, o)) f = uncurry (set #acOutput) (runState (f o) c)

----------------------------- MonadCircuit instance ----------------------------

instance Finite a => Witness (Var a i) (WitnessF a (WitVar p i)) where
  at (ConstVar cV)   = fromConstant cV
  at (LinVar k sV b) = fromConstant k * pure (WSysVar sV) + fromConstant b

instance
  ( Arithmetic a, Binary a, Binary (Rep p), Binary (Rep i), Ord (Rep i)
  , o ~ U1) => MonadCircuit (Var a i) a (WitnessF a (WitVar p i)) (State (ArithmeticCircuit a p i o)) where

    unconstrained wf =
        case runWitnessF wf $ \case
          WSysVar sV -> LinUVar one sV zero
          _          -> More
        of
          LinUVar k x b -> return (LinVar k x b)
          _ -> do
            let v = witToVar @a wf
            -- TODO: forbid reassignment of variables
            zoom #acWitness $ modify (insert v wf)
            return $ toVar (NewVar v)

    constraint p =
      let evalConstVar = \case
            LinVar k sysV b -> fromConstant k * var sysV + fromConstant b
            ConstVar cV -> fromConstant cV
          evalMaybe = \case
            ConstVar cV -> Just cV
            _ -> Nothing
      in case p evalMaybe of
        Just c -> if c == zero
                    then return ()
                    else error "The constraint is non-zero"
        Nothing -> zoom #acSystem . modify $ insert (witToVar @_ @p (p at)) (p evalConstVar)

    rangeConstraint (LinVar k x b) upperBound = do
      v <- preparedVar
      zoom #acRange . modify $ insertWith S.union upperBound (S.singleton v)
      where
        preparedVar = if k == one && b == zero || k == negate one && b == upperBound
          then return x
          else do
            let
              wf = at $ LinVar k x b
              v = witToVar @a wf
            -- TODO: forbid reassignment of variables
            zoom #acWitness $ modify (insert v wf)
            return (NewVar v)

    rangeConstraint (ConstVar c) upperBound =
      if c <= upperBound
        then return ()
        else error "The constant does not belong to the interval"

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
witToVar ::
  forall a p i. (Finite a, Binary a, Binary (Rep p), Binary (Rep i)) =>
  WitnessF a (WitVar p i) -> ByteString
witToVar (WitnessF w) = runHash @(Just (Order a)) $ w $ \case
  WExVar exV -> merkleHash exV
  WSysVar (InVar inV) -> merkleHash inV
  WSysVar (NewVar newV) -> M newV

----------------------------- Evaluation functions -----------------------------

witnessGenerator ::
  (Arithmetic a, Representable p, Representable i) =>
  ArithmeticCircuit a p i o -> p a -> i a -> Map ByteString a
witnessGenerator circuit payload inputs =
  let result = acWitness circuit <&> \k -> runWitnessF k $ \case
        WExVar eV -> index payload eV
        WSysVar (InVar iV) -> index inputs iV
        WSysVar (NewVar nV) -> result ! nV
  in result

-- | Evaluates the arithmetic circuit with one output using the supplied input map.
eval1 ::
  (Arithmetic a, Representable p, Representable i) =>
  ArithmeticCircuit a p i Par1 -> p a -> i a -> a
eval1 ctx p i = unPar1 (eval ctx p i)

-- | Evaluates the arithmetic circuit using the supplied input map.
eval ::
  (Arithmetic a, Representable p, Representable i, Functor o) =>
  ArithmeticCircuit a p i o -> p a -> i a -> o a
eval ctx p i = indexW ctx p i <$> acOutput ctx

-- | Evaluates the arithmetic circuit with no inputs and one output.
exec1 :: Arithmetic a => ArithmeticCircuit a U1 U1 Par1 -> a
exec1 ac = eval1 ac U1 U1

-- | Evaluates the arithmetic circuit with no inputs.
exec :: (Arithmetic a, Functor o) => ArithmeticCircuit a U1 U1 o -> o a
exec ac = eval ac U1 U1

-- | Applies the values of the first couple of inputs to the arithmetic circuit.
apply ::
  (Eq a, Field a, Ord (Rep j), Representable i) =>
  i a -> ArithmeticCircuit a p (i :*: j) U1 -> ArithmeticCircuit a p j U1
apply xs ac = ac
  { acSystem = fmap (evalPolynomial evalMonomial varF) (acSystem ac)
  , acRange = S.fromList . catMaybes . toList . filterSet <$> acRange ac
  , acWitness = (>>= witF) <$> acWitness ac
  , acOutput = U1
  }
  where
    varF (InVar (Left v))  = fromConstant (index xs v)
    varF (InVar (Right v)) = var (InVar v)
    varF (NewVar v)        = var (NewVar v)

    witF (WSysVar (InVar (Left v)))  = WitnessF $ const $ fromConstant (index xs v)
    witF (WSysVar (InVar (Right v))) = pure $ WSysVar (InVar v)
    witF (WSysVar (NewVar v))        = pure $ WSysVar (NewVar v)
    witF (WExVar v)                  = pure (WExVar v)

    filterSet :: Ord (Rep j) => S.Set (SysVar (i :*: j)) ->  S.Set (Maybe (SysVar j))
    filterSet = S.map (\case
                    NewVar v        -> Just (NewVar v)
                    InVar (Right v) -> Just (InVar v)
                    _               -> Nothing)

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
