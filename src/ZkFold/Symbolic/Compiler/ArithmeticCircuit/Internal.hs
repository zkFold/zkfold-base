{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Circuit (..),
        Arithmetic,
        ConstraintMonomial,
        Constraint,

        withOutputs,
        constraintSystem,
        inputVariables,
        witnessGenerator,
        varOrder,
        -- low-level functions
        constraint,
        rangeConstraint,
        assignment,
        addVariable,
        newVariableWithSource,
        eval,
        eval1,
        exec,
        exec1,
        apply,
        forceZero,
    ) where

import           Control.DeepSeq                              (NFData, force)
import           Control.Monad.State                          (MonadState (..), State, gets, modify, runState)
import           Data.Map.Strict                              hiding (drop, foldl, foldr, map, null, splitAt, take)
import qualified Data.Map.Strict                              as M
import qualified Data.Set                                     as S
import           GHC.Generics                                 (Generic, Par1 (..))
import           Optics
import           Prelude                                      hiding (Num (..), drop, length, product, splitAt, sum,
                                                               take, (!!), (^))
import qualified Prelude                                      as Haskell
import           System.Random                                (StdGen, mkStdGen, uniform, uniformR)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Sources
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Mono, Poly, evalMonomial, evalPolynomial, mapCoeffs, var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Base.Data.Vector                      (Vector (..))
import           ZkFold.Prelude                               (drop, length)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.MonadCircuit

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data Circuit a = Circuit
    {
        acSystem   :: Map Natural (Constraint a),
        -- ^ The system of polynomial constraints
        acRange    :: Map Natural a,
        -- ^ The range constraints [0, a] for the selected variables
        acInput    :: [Natural],
        -- ^ The input variables
        acWitness  :: Map Natural (Map Natural a -> a),
        -- ^ The witness generation functions
        acVarOrder :: Map (Natural, Natural) Natural,
        -- ^ The order of variable assignments
        acRNG      :: StdGen
    } deriving (Generic, NFData)

data ArithmeticCircuit a f = ArithmeticCircuit
  { acCircuit :: Circuit a
  , acOutput  :: f Natural
  } deriving (Generic)

deriving instance (NFData a, NFData (f Natural)) => NFData (ArithmeticCircuit a f)

withOutputs :: Circuit a -> f Natural -> ArithmeticCircuit a f
withOutputs = ArithmeticCircuit

constraintSystem :: ArithmeticCircuit a f -> Map Natural (Constraint a)
constraintSystem = acSystem . acCircuit

inputVariables :: ArithmeticCircuit a f -> [Natural]
inputVariables = acInput . acCircuit

witnessGenerator :: ArithmeticCircuit a f -> Map Natural a -> Map Natural a
witnessGenerator circuit inputs =
  let srcs = acWitness (acCircuit circuit)
      witness = ($ witness) <$> (srcs `union` fmap const inputs)
   in witness

varOrder :: ArithmeticCircuit a f -> Map (Natural, Natural) Natural
varOrder = acVarOrder . acCircuit

------------------------------ Symbolic compiler context ----------------------------

instance HFunctor (ArithmeticCircuit a) where
    hmap f (ArithmeticCircuit c o) = ArithmeticCircuit c (f o)

instance (Eq a, MultiplicativeMonoid a) => HApplicative (ArithmeticCircuit a) where
    hpure = ArithmeticCircuit mempty
    hliftA2 f (ArithmeticCircuit c o) (ArithmeticCircuit d p) = ArithmeticCircuit (c <> d) (f o p)

instance (Eq a, MultiplicativeMonoid a) => Package (ArithmeticCircuit a) where
    unpackWith f (ArithmeticCircuit c o) = ArithmeticCircuit c <$> f o
    packWith f = ArithmeticCircuit <$> foldMap acCircuit <*> f . fmap acOutput

type Arithmetic a = (SymbolicField a, Eq a)

instance Arithmetic a => Symbolic (ArithmeticCircuit a) where
    type BaseField (ArithmeticCircuit a) = a
    symbolicF (ArithmeticCircuit c o) _ f = let (p, d) = runState (f o) c in withOutputs d p

-------------------------------- MonadCircuit instance ------------------------------

instance Arithmetic a => MonadCircuit Natural a (State (Circuit a)) where
    newRanged upperBound witness = do
        let s   = sources @a witness
            -- | A wild (and obviously incorrect) approximation of
            -- x (x - 1) ... (x - upperBound)
            -- It's ok because we only use it for variable generation anyway.
            p i = var i * (var i - fromConstant upperBound)
        i <- addVariable =<< newVariableWithSource (S.toList s) p
        rangeConstraint i upperBound
        assignment i (\m -> witness (m !))
        return i

    newConstrained
        :: NewConstraint Natural a
        -> Witness Natural a
        -> State (Circuit a) Natural
    newConstrained new witness = do
        let ws = sources @a witness
            -- | We need a throwaway variable to feed into `new` which definitely would not be present in a witness
            x = maximum (S.mapMonotonic (+1) ws <> S.singleton 0)
            -- | `s` is meant to be a set of variables used in a witness not present in a constraint.
            s = ws `S.difference` sources @a (`new` x)
        i <- addVariable =<< newVariableWithSource (S.toList s) (new var)
        constraint (`new` i)
        assignment i (\m -> witness (m !))
        return i

    constraint p = addConstraint (p var)

sources :: forall a i . (FiniteField a, Ord i) => Witness i a -> S.Set i
sources = runSources . ($ Sources @a . S.singleton)

----------------------------------- Circuit monoid ----------------------------------

instance Eq a => Semigroup (Circuit a) where
    c1 <> c2 =
        Circuit
           {
               acSystem   = acSystem c1 `union` acSystem c2
            ,  acRange    = acRange c1 `union` acRange c2
               -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
               -- We need a way to ensure the correct order no matter how `(<>)` is used.
           ,   acInput    = nubConcat (acInput c1) (acInput c2)
           ,   acWitness  = acWitness c1 `union` acWitness c2
           ,   acVarOrder = acVarOrder c1 `union` acVarOrder c2
           ,   acRNG      = mkStdGen $ fst (uniform (acRNG c1)) Haskell.* fst (uniform (acRNG c2))
           }

nubConcat :: Ord a => [a] -> [a] -> [a]
nubConcat l r = l ++ Prelude.filter (`S.notMember` lSet) r
    where
        lSet = S.fromList l

instance (Eq a, MultiplicativeMonoid a) => Monoid (Circuit a) where
    mempty =
        Circuit
           {
               acSystem   = empty,
               acRange    = empty,
               acInput    = [],
               acWitness  = singleton 0 one,
               acVarOrder = empty,
               acRNG      = mkStdGen 0
           }

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = Zp BLS12_381_Scalar

toField :: Arithmetic a => a -> VarField
toField = toZp . fromConstant . fromBinary @Natural . castBits . binaryExpansion

-- TODO: Remove the hardcoded constant.
toVar :: Arithmetic a => [Natural] -> Constraint a -> Natural
toVar srcs c = force $ fromZp ex
    where
        r  = toZp 903489679376934896793395274328947923579382759823 :: VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: VarField
        v  = (+ r) . fromConstant
        x  = g ^ fromZp (evalPolynomial evalMonomial v $ mapCoeffs toField c)
        ex = foldr (\p y -> x ^ p + y) x srcs

newVariableWithSource :: Arithmetic a => [Natural] -> (Natural -> Constraint a) -> State (Circuit a) Natural
newVariableWithSource srcs con = toVar srcs . con . fst <$> do
    zoom #acRNG $ get >>= traverse put . uniformR (0, order @VarField -! 1)

addVariable :: Natural -> State (Circuit a) Natural
addVariable x = do
    zoom #acVarOrder . modify
        $ \vo -> insert (Haskell.fromIntegral $ M.size vo, x) x vo
    pure x

---------------------------------- Low-level functions --------------------------------

type ConstraintMonomial = Mono Natural Natural

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c = Poly c Natural Natural

-- | Adds a constraint to the arithmetic circuit.
addConstraint :: Arithmetic a => Constraint a -> State (Circuit a) ()
addConstraint c = zoom #acSystem . modify $ insert (toVar [] c) c

rangeConstraint :: Natural -> a -> State (Circuit a) ()
rangeConstraint i b = zoom #acRange . modify $ insert i b

-- | Forces the provided variables to be zero.
forceZero :: Arithmetic a => Vector n Natural -> State (Circuit a) ()
forceZero = mapM_ (addConstraint . var)

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: Natural -> (Map Natural a -> a) -> State (Circuit a) ()
assignment i f = zoom #acWitness . modify $ insert i f

-- | Evaluates the arithmetic circuit with one output using the supplied input map.
eval1 :: ArithmeticCircuit a Par1 -> Map Natural a -> a
eval1 ctx i = witnessGenerator ctx i ! unPar1 (acOutput ctx)

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: Functor f => ArithmeticCircuit a f -> Map Natural a -> f a
eval ctx i = (witnessGenerator ctx i !) <$> acOutput ctx

-- | Evaluates the arithmetic circuit with no inputs and one output using the supplied input map.
exec1 :: ArithmeticCircuit a Par1 -> a
exec1 ac = eval1 ac empty

-- | Evaluates the arithmetic circuit with no inputs using the supplied input map.
exec :: Functor f => ArithmeticCircuit a f -> f a
exec ac = eval ac empty

-- | Applies the values of the first `n` inputs to the arithmetic circuit.
-- TODO: make this safe
apply :: [a] -> State (Circuit a) ()
apply xs = do
    inputs <- gets acInput
    zoom #acInput . put $ drop (length xs) inputs
    zoom #acWitness . modify . union . fromList $ zip inputs (map const xs)

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
