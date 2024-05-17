{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Arithmetic,
        ConstraintMonomial,
        Constraint,
        -- low-level functions
        constraint,
        assignment,
        addVariable,
        newVariableWithSource,
        input,
        eval,
        apply,
        forceZero
    ) where

import           Control.DeepSeq                              (NFData)
import           Control.Monad.State                          (MonadState (..), State, modify)
import           Data.List                                    (nub)
import           Data.Map.Strict                              hiding (drop, foldl, foldr, map, null, splitAt, take)
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
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Monomial', Polynomial', evalMapM, evalPolynomial,
                                                               mapCoeffs, var)
import           ZkFold.Prelude                               (drop, length)

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a = ArithmeticCircuit
    {
        acSystem   :: Map Natural (Constraint a),
        -- ^ The system of polynomial constraints
        acInput    :: [Natural],
        -- ^ The input variables
        acWitness  :: Map Natural a -> Map Natural a,
        -- ^ The witness generation function
        acOutput   :: Natural,
        -- ^ The output variable
        acVarOrder :: Map (Natural, Natural) Natural,
        -- ^ The order of variable assignments
        acRNG      :: StdGen
    } deriving (Generic, NFData)

----------------------------------- Circuit monoid ----------------------------------

instance Eq a => Semigroup (ArithmeticCircuit a) where
    r1 <> r2 = ArithmeticCircuit
        {
            acSystem   = acSystem r1 `union` acSystem r2,
            -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
            -- We need a way to ensure the correct order no matter how `(<>)` is used.
            acInput    = nub $ acInput r1 ++ acInput r2,
            acWitness  = union <$> acWitness r1 <*> acWitness r2,
            acOutput   = max (acOutput r1) (acOutput r2),
            acVarOrder = acVarOrder r1 `union` acVarOrder r2,
            acRNG      = mkStdGen $ fst (uniform (acRNG r1)) Haskell.* fst (uniform (acRNG r2))
        }

instance (FiniteField a, Eq a) => Monoid (ArithmeticCircuit a) where
    mempty = ArithmeticCircuit
        {
            acSystem   = empty,
            acInput    = [],
            acWitness  = insert 0 one,
            acOutput   = 0,
            acVarOrder = empty,
            acRNG      = mkStdGen 0
        }

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = Zp BLS12_381_Scalar

toField :: Arithmetic a => a -> VarField
toField = toZp . fromConstant . fromBinary @Natural . castBits . binaryExpansion

type Arithmetic a = (FiniteField a, Eq a, BinaryExpansion a, DiscreteField a)

-- TODO: Remove the hardcoded constant.
toVar :: forall a . Arithmetic a => [Natural] -> Constraint a -> Natural
toVar srcs c = fromZp ex
    where
        r  = toZp 903489679376934896793395274328947923579382759823 :: VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: VarField
        v  = (+ r) . fromConstant
        x  = g ^ fromZp (evalPolynomial evalMapM v $ mapCoeffs toField c)
        ex = foldr (\p y -> x ^ p + y) x srcs

newVariableWithSource :: Arithmetic a => [Natural] -> (Natural -> Constraint a) -> State (ArithmeticCircuit a) Natural
newVariableWithSource srcs con = toVar srcs . con . fst <$> do
    zoom #acRNG $ get >>= traverse put . uniformR (0, order @VarField -! 1)

addVariable :: Natural -> State (ArithmeticCircuit a) Natural
addVariable x = do
    zoom #acOutput $ put x
    zoom #acVarOrder . modify
        $ \vo -> insert (length vo, x) x vo
    pure x

---------------------------------- Low-level functions --------------------------------

type ConstraintMonomial = Monomial'

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c = Polynomial' c

-- | Adds a constraint to the arithmetic circuit.
constraint :: Arithmetic a => Constraint a -> State (ArithmeticCircuit a) ()
constraint c = zoom #acSystem . modify $ insert (toVar [] c) c

-- | Forces the current variable to be zero.
forceZero :: forall a . Arithmetic a => State (ArithmeticCircuit a) ()
forceZero = zoom #acOutput get >>= constraint . var

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: (Map Natural a -> a) -> State (ArithmeticCircuit a) ()
assignment f = do
    i <- insert <$> zoom #acOutput get
    zoom #acWitness . modify $ (.) (\m -> i (f m) m)

-- | Adds a new input variable to the arithmetic circuit. Returns a copy of the arithmetic circuit with this variable as output.
input :: forall a . State (ArithmeticCircuit a) (ArithmeticCircuit a)
input = do
  inputs <- zoom #acInput get
  let s = if null inputs then 1 else maximum inputs + 1
  zoom #acInput $ modify (++ [s])
  zoom #acOutput $ put s
  zoom #acVarOrder $ put $ singleton (0, s) s
  get

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: ArithmeticCircuit a -> Map Natural a -> a
eval ctx i = acWitness ctx i ! acOutput ctx

-- | Applies the values of the first `n` inputs to the arithmetic circuit.
-- TODO: make this safe
apply :: [a] -> State (ArithmeticCircuit a) ()
apply xs = do
    inputs <- zoom #acInput get
    zoom #acInput . put $ drop (length xs) inputs
    zoom #acWitness . modify $ (. union (fromList $ zip inputs xs))

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
