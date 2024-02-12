{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Arithmetic,
        Constraint,
        -- low-level functions
        constraint,
        assignment,
        addVariable,
        newVariableWithSource,
        newVariableFromConstraint,
        input,
        eval,
        apply,
        forceZero
    ) where

import           Control.Monad.State                          (MonadState (..), State, modify)
import           Data.Map                                     hiding (take, drop, splitAt, foldl, null, map, foldr)
import           Prelude                                      hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)
import           System.Random                                (StdGen, Random (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp, toZp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Polynomial, variableList, evalMultivariate, monomial, polynomial)
import           ZkFold.Prelude                               (length, drop, take)

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a = ArithmeticCircuit
    {
        acSystem   :: Map Integer (Constraint a),
        -- ^ The system of polynomial constraints
        acInput    :: [Integer],
        -- ^ The input variables
        acWitness  :: Map Integer a -> Map Integer a,
        -- ^ The witness generation function
        acOutput   :: Integer,
        -- ^ The output variable
        acVarOrder :: Map (Integer, Integer) Integer,
        -- ^ The order of variable assignments
        acRNG      :: StdGen
    }

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = BLS12_381_Scalar

class (FiniteField a, Eq a, ToBits a, Scale (Zp VarField) a) => Arithmetic a

instance (FiniteField a, Eq a, ToBits a, Scale (Zp VarField) a) => Arithmetic a

-- TODO: Remove the hardcoded constant.
toVar :: Scale (Zp VarField) a => [Integer] -> Constraint a -> Integer
toVar srcs c = fromBits $ castBits $ toBits ex
    where
        r  = toZp 903489679376934896793395274328947923579382759823 :: Zp VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: Zp VarField
        zs = variableList c
        vs = fromList $ zip zs (map ((+) r . toZp) zs)
        x  = g ^ (c `evalMultivariate` vs)
        ex = foldr (\p y -> x ^ p + y) x srcs

con2var :: Scale (Zp VarField) a => Constraint a -> Integer
con2var = toVar []

newVariable :: State (ArithmeticCircuit a) Integer
newVariable = do
    r <- get
    let (x, g) = randomR (0, order @VarField - 1) (acRNG r)
    put r { acRNG = g }
    return x

newVariableFromConstraint :: Scale (Zp VarField) a => (Integer -> Constraint a) -> State (ArithmeticCircuit a) Integer
newVariableFromConstraint = newVariableWithSource []

newVariableWithSource :: Scale (Zp VarField) a => [Integer] -> (Integer -> Constraint a) -> State (ArithmeticCircuit a) Integer
newVariableWithSource srcs con = toVar srcs . con <$> newVariable

addVariable :: Integer -> State (ArithmeticCircuit a) ()
addVariable x = modify (\r -> r { acOutput = x, acVarOrder = insert (length (acVarOrder r), x) x (acVarOrder r)})

---------------------------------- Low-level functions --------------------------------

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint a = Polynomial a

-- | Adds a constraint to the arithmetic circuit.
constraint :: Scale (Zp VarField) a => Constraint a -> State (ArithmeticCircuit a) ()
constraint con = modify $ \r -> r { acSystem = insert (con2var con) con (acSystem r) }

-- | Forces the current variable to be zero.
forceZero :: forall a . Arithmetic a => State (ArithmeticCircuit a) ()
forceZero = do
    r <- get
    let x   = acOutput r
        con = polynomial [monomial one (singleton x one)]
    constraint con

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: forall a . (Map Integer a -> a) -> State (ArithmeticCircuit a) ()
assignment f = modify $ \r -> r { acWitness = \i -> insert (acOutput r) (f i) (acWitness r i) }

-- | Adds a new input variable to the arithmetic circuit. Returns a copy of the arithmetic circuit with this variable as output.
input :: forall a . State (ArithmeticCircuit a) (ArithmeticCircuit a)
input = modify (\(r :: ArithmeticCircuit a) ->
        let ins    = acInput r
            s      = if null ins then 1 else maximum (acInput r) + 1
        in r
        {
            acInput    = ins ++ [s],
            acOutput   = s,
            acVarOrder = singleton (0, s) s
        }) >> get

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: ArithmeticCircuit a -> Map Integer a -> a
eval ctx i =
    let w = acWitness ctx i
        o = acOutput ctx
    in w ! o

-- | Applies the values of the first `n` inputs to the arithmetic circuit.
-- TODO: make this safe
apply :: [a] -> State (ArithmeticCircuit a) ()
apply xs = modify (\(r :: ArithmeticCircuit a) ->
    let ins = acInput r
        n   = length xs
    in r
    {
        acInput = drop n ins,
        acWitness = acWitness r . (fromList (zip (take n ins) xs) `union`)
    })

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
