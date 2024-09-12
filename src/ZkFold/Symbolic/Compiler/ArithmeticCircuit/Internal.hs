{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Var (..),
        SysVar (..),
        acInput,
        Arithmetic,
        ConstraintMonomial,
        Constraint,
        witnessGenerator,
        -- low-level functions
        constraint,
        rangeConstraint,
        assignment,
        newVariableWithSource,
        eval,
        eval1,
        exec,
        exec1,
        apply,
        getAllVars,
        genVarSet,
        indexW
    ) where

import           Control.DeepSeq                              (NFData, force)
import           Control.Monad.State                          (MonadState (..), State, modify, runState)
import           Data.Aeson
import           Data.Containers.ListUtils                    (nubOrd)
import           Data.Foldable                                (fold, toList)
import           Data.Functor.Rep
import           Data.List                                    (sort)
import           Data.Map.Strict                              hiding (drop, foldl, foldr, map, mapMaybe, null, splitAt,
                                                               take, toList)
import qualified Data.Map.Strict                              as M
import           Data.Maybe                                   (fromMaybe)
import           Data.Semialign                               (unzipDefault)
import qualified Data.Set                                     as S
import           GHC.Generics                                 (Generic, Par1 (..), U1 (..), (:*:) (..))
import           Optics                                       hiding (ix)
import           Prelude                                      hiding (Num (..), drop, length, product, splitAt, sum,
                                                               take, (!!), (^))
import qualified Prelude                                      as Haskell
import           System.Random                                (StdGen, mkStdGen, uniform, uniformR)
import           Test.QuickCheck                              (Gen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Sources
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Mono, Poly, evalMonomial, evalPolynomial, mapCoeffs, var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Prelude                               (genSubset)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.MonadCircuit

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a i o = ArithmeticCircuit
    {
        acSystem  :: Map Natural (Constraint a i),
        -- ^ The system of polynomial constraints
        acRange   :: Map Natural a,
        -- ^ The range constraints [0, a] for the selected variables
        acWitness :: Map Natural (i a -> Map Natural a -> a),
        -- ^ The witness generation functions
        acRNG     :: StdGen,
        -- ^ random generator for generating unique variables
        acOutput  :: o (Var a i)
        -- ^ The output variables
    } deriving (Generic)
deriving instance (NFData a, NFData (o (Var a i)), NFData (Rep i))
    => NFData (ArithmeticCircuit a i o)

acInput0 :: Representable i => i (SysVar i)
acInput0 = fmapRep InVar (tabulate id)

acInput :: Representable i => i (Var a i)
acInput = fmapRep (SysVar . InVar) (tabulate id)

data SysVar i
  = InVar (Rep i)
  | NewVar Natural
  deriving Generic
deriving anyclass instance FromJSON (Rep i) => FromJSON (SysVar i)
deriving anyclass instance FromJSON (Rep i) => FromJSONKey (SysVar i)
deriving anyclass instance ToJSON (Rep i) => ToJSONKey (SysVar i)
deriving anyclass instance ToJSON (Rep i) => ToJSON (SysVar i)
deriving stock instance Show (Rep i) => Show (SysVar i)
deriving stock instance Eq (Rep i) => Eq (SysVar i)
deriving stock instance Ord (Rep i) => Ord (SysVar i)
deriving instance NFData (Rep i) => NFData (SysVar i)

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

witnessGenerator :: ArithmeticCircuit a i o -> i a -> Map Natural a
witnessGenerator circuit inputs =
    let
        result = fmap (\k -> k inputs result) (acWitness circuit)
    in
        result

--------------------------- Symbolic compiler context --------------------------

indexW :: Representable i => ArithmeticCircuit a i o -> i a -> Var a i -> a
indexW circuit inputs = \case
  SysVar (InVar j) -> index inputs j
  SysVar (NewVar j) -> fromMaybe
    (error ("no such NewVar: " <> show j))
    (witnessGenerator circuit inputs M.!? j)
  ConstVar c -> c

crown :: ArithmeticCircuit a i g -> f (Var a i) -> ArithmeticCircuit a i f
crown = flip (set #acOutput)

behead :: ArithmeticCircuit a i f -> (ArithmeticCircuit a i U1, f (Var a i))
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
  ( Arithmetic a, Ord (Rep i), Representable i, Foldable i
  , ToConstant (Rep i), Const (Rep i) ~ Natural
  ) => Symbolic (ArithmeticCircuit a i) where
    type BaseField (ArithmeticCircuit a i) = a
    symbolicF (behead -> (c, o)) _ f = uncurry (set #acOutput) (runState (f o) c)

----------------------------- MonadCircuit instance ----------------------------

instance
  ( Arithmetic a, Ord (Rep i), Representable i, Foldable i, o ~ U1
  , ToConstant (Rep i), Const (Rep i) ~ Natural
  ) => MonadCircuit (Var a i) a (State (ArithmeticCircuit a i o)) where
    newRanged upperBound witness' = do
        let s   = sources @a witness
            b   = fromConstant upperBound
            -- | A wild (and obviously incorrect) approximation of
            -- x (x - 1) ... (x - upperBound)
            -- It's ok because we only use it for variable generation anyway.
            p i = b * var i * (var i - b)
            evalConst :: FromConstant a x => (SysVar i -> x) -> Var a i -> x
            evalConst ix = \case
              SysVar v -> ix v
              ConstVar c -> fromConstant c
            witness :: Witness (SysVar i) a
            witness ix = witness' (evalConst ix)
        i <- newVariableWithSource (S.toList s) p
        rangeConstraint i upperBound
        assignment i $ \m currentWitness -> witness $ \case
          InVar inV -> index m inV
          NewVar newV -> currentWitness ! newV
        return (SysVar (NewVar i))

    newConstrained
        :: NewConstraint (Var a i) a
        -> Witness (Var a i) a
        -> State (ArithmeticCircuit a i U1) (Var a i)
    newConstrained new' witness' = do
        let evalConst :: FromConstant a x => (SysVar i -> x) -> Var a i -> x
            evalConst ix = \case
              SysVar v -> ix v
              ConstVar c -> fromConstant c
            new :: NewConstraint (SysVar i) a
            new ix i = new' (evalConst ix) (SysVar i)
            witness :: Witness (SysVar i) a
            witness ix = witness' (evalConst ix)
            ws :: S.Set (SysVar i) = sources @a witness
            varF (NewVar v) = NewVar (v + 1)
            varF (InVar v)  = InVar v
            -- | We need a throwaway variable to feed into `new` which definitely would not be present in a witness
            x = maximum (S.mapMonotonic varF ws <> S.singleton (NewVar 0))
            -- | `s` is meant to be a set of variables used in a witness not present in a constraint.
            s = ws `S.difference` sources @a (`new` x)
        i <- newVariableWithSource (S.toList s) (new var)
        constraint (`new'` (SysVar (NewVar i)))
        assignment i $ \m currentWitness -> witness $ \case
          InVar inV -> index m inV
          NewVar newV -> currentWitness ! newV
        return (SysVar (NewVar i))

    constraint p =
      let
        evalVar :: Var a i -> Constraint a i
        evalVar = \case
            SysVar v -> var v
            ConstVar c -> fromConstant c
      in
        addConstraint (p evalVar)

sources :: forall a i . (FiniteField a, Ord i) => Witness i a -> S.Set i
sources = runSources . ($ Sources @a . S.singleton)

----------------------------------- Circuit monoid ----------------------------------

instance o ~ U1 => Semigroup (ArithmeticCircuit a i o) where
    c1 <> c2 =
        ArithmeticCircuit
           {   acSystem   = acSystem c1 `union` acSystem c2
           ,   acRange    = acRange c1 `union` acRange c2
           ,   acWitness  = acWitness c1 `union` acWitness c2
           ,   acRNG      = mkStdGen $ fst (uniform (acRNG c1)) Haskell.* fst (uniform (acRNG c2))
           ,   acOutput   = U1
           }

instance o ~ U1 => Monoid (ArithmeticCircuit a i o) where
    mempty =
        ArithmeticCircuit
           {
               acSystem   = empty,
               acRange    = empty,
               acWitness  = empty,
               acRNG      = mkStdGen 0,
               acOutput   = U1
           }

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = Zp BLS12_381_Scalar

toField :: Arithmetic a => a -> VarField
toField = fromConstant . toConstant

-- TODO: Remove the hardcoded constant.
toVar ::
  forall a i.
  (Arithmetic a, ToConstant (Rep i), Const (Rep i) ~ Natural) =>
  (Representable i, Foldable i) => [SysVar i] -> Constraint a i -> Natural
toVar srcs c = force $ fromZp ex
    where
        l  = Haskell.fromIntegral (Haskell.length (tabulate @i (\_ -> error "can't reach")))
        r  = toZp 903489679376934896793395274328947923579382759823 :: VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: VarField
        varF (NewVar w)  = w + l
        varF (InVar inV) = toConstant inV
        v  = (+ r) . fromConstant . varF
        x  = g ^ fromZp (evalPolynomial evalMonomial v $ mapCoeffs toField c)
        ex = foldr (\p y -> x ^ varF p + y) x srcs

newVariableWithSource ::
  (Arithmetic a, ToConstant (Rep i), Const (Rep i) ~ Natural) =>
  (Representable i, Foldable i) =>
  [SysVar i] -> (SysVar i -> Constraint a i) ->
  State (ArithmeticCircuit a i U1) Natural
newVariableWithSource srcs con = toVar srcs . con . NewVar . fst <$> do
    zoom #acRNG $ get >>= traverse put . uniformR (0, order @VarField -! 1)

---------------------------------- Low-level functions --------------------------------

type ConstraintMonomial = Mono Natural Natural

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c i = Poly c (SysVar i) Natural

-- | Adds a constraint to the arithmetic circuit.
addConstraint ::
  (Arithmetic a, Foldable i, Representable i) =>
  (ToConstant (Rep i), Const (Rep i) ~ Natural) =>
  Constraint a i -> State (ArithmeticCircuit a i U1) ()
addConstraint c = zoom #acSystem . modify $ insert (toVar [] c) c

rangeConstraint :: Natural -> a -> State (ArithmeticCircuit a i U1) ()
rangeConstraint i b = zoom #acRange . modify $ insert i b

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: Natural -> (i a -> Map Natural a -> a) -> State (ArithmeticCircuit a i U1) ()
assignment i f = zoom #acWitness . modify $ insert i f

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
apply :: (Eq a, Field a, Ord (Rep j), Representable i) => i a -> ArithmeticCircuit a (i :*: j) U1 -> ArithmeticCircuit a j U1
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

    -- let inputs = acInput
    -- zoom #acWitness . modify . union . fromList $ zip inputs (map const xs)

getAllVars :: (Ord (Rep i), Representable i, Foldable i) => ArithmeticCircuit a i o -> [SysVar i]
getAllVars ac = nubOrd $ sort $ toList acInput0 ++ map NewVar (keys $ acWitness ac)

genVarSet :: (Ord (Rep i), Representable i, Foldable i) => Natural -> ArithmeticCircuit a i o -> Gen [SysVar i]
genVarSet l = genSubset l . getAllVars

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
