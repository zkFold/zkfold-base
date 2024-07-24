{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

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
        mapOutputs,
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
        joinCircuits,
        concatCircuits
    ) where

import           Control.DeepSeq                              (NFData, force)
import           Control.Monad.State                          (MonadState (..), State, gets, modify)
import           Data.Map.Strict                              hiding (drop, foldl, foldr, map, null, splitAt, take)
import qualified Data.Set                                     as S
import           GHC.Generics
import           Numeric.Natural                              (Natural)
import           Optics
import           Prelude                                      hiding (Num (..), drop, length, product, splitAt, sum,
                                                               take, (!!), (^))
import qualified Prelude                                      as Haskell
import           System.Random                                (StdGen, mkStdGen, uniform, uniformR)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Mono, Poly, evalMonomial, evalPolynomial, mapCoeffs, var)
import           ZkFold.Base.Data.Vector                      (Vector (..))
import           ZkFold.Prelude                               (drop, length)

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

mapOutputs :: (forall i . f i -> g i) -> ArithmeticCircuit a f -> ArithmeticCircuit a g
mapOutputs f (ArithmeticCircuit ac o) = ArithmeticCircuit ac (f o)

----------------------------------- Circuit monoid ----------------------------------

instance Eq a => Semigroup (Circuit a) where
    c1 <> c2 =
        Circuit
           {
               acSystem   = {-# SCC system_union #-}    acSystem c1 `union` acSystem c2
            ,  acRange    = {-# SCC range_union #-}     acRange c1 `union` acRange c2
               -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
               -- We need a way to ensure the correct order no matter how `(<>)` is used.
           ,   acInput    = {-# SCC input_union #-}     nubConcat (acInput c1) (acInput c2)
           ,   acWitness  = {-# SCC witness_union #-}   acWitness c1 `union` acWitness c2
           ,   acVarOrder = {-# SCC var_order_union #-} acVarOrder c1 `union` acVarOrder c2
           ,   acRNG      = {-# SCC rng_union #-}       mkStdGen $ fst (uniform (acRNG c1)) Haskell.* fst (uniform (acRNG c2))
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

joinCircuits :: Eq a => ArithmeticCircuit a ol -> ArithmeticCircuit a or -> ArithmeticCircuit a (ol :*: or)
joinCircuits r1 r2 =
    ArithmeticCircuit
        {
            acCircuit = acCircuit r1 <> acCircuit r2
        ,   acOutput = acOutput r1 :*: acOutput r2
        }

concatCircuits :: (Eq a, MultiplicativeMonoid a, Foldable f, Functor f) => f (ArithmeticCircuit a g) -> ArithmeticCircuit a (f :.: g)
concatCircuits cs =
    ArithmeticCircuit
        {
            acCircuit = foldMap acCircuit cs
        ,   acOutput = Comp1 (acOutput <$> cs)
        }

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = Zp BLS12_381_Scalar

toField :: Arithmetic a => a -> VarField
toField = toZp . fromConstant . fromBinary @Natural . castBits . binaryExpansion

type Arithmetic a = (FiniteField a, Eq a, BinaryExpansion a, Bits a ~ [a])

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
        $ \vo -> insert (length vo, x) x vo
    pure x

---------------------------------- Low-level functions --------------------------------

type ConstraintMonomial = Mono Natural Natural

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c = Poly c Natural Natural

-- | Adds a constraint to the arithmetic circuit.
constraint :: Arithmetic a => Constraint a -> State (Circuit a) ()
constraint c = zoom #acSystem . modify $ insert (toVar [] c) c

rangeConstraint :: Natural -> a -> State (Circuit a) ()
rangeConstraint i b = zoom #acRange . modify $ insert i b

-- | Forces the provided variables to be zero.
forceZero :: Arithmetic a => Vector n Natural -> State (Circuit a) ()
forceZero = mapM_ (constraint . var)

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
