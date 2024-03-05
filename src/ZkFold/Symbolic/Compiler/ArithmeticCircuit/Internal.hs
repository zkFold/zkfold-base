{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

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

import           Control.Monad.State                          (MonadState (..), State, modify)
import           Data.List                                    (nub)
import           Data.Map                                     hiding (take, drop, splitAt, foldl, null, map, foldr)
import           GHC.Generics
import           Optics
import           Prelude                                      hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)
import qualified Prelude                                      as Haskell
import           System.Random                                (Random (..), StdGen, mkStdGen, uniform)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp, toZp)
import           ZkFold.Base.Algebra.Basic.Scale              (BinScale(..))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (SomeMonomial, SomePolynomial, monomial, polynomial, evalPolynomial, var)
import           ZkFold.Prelude                               (length, drop)

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
    } deriving Generic

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
type VarField = BLS12_381_Scalar

type Arithmetic a = (FiniteField a, Eq a, BinaryExpansion a)

-- TODO: Remove the hardcoded constant.
toVar :: forall a . Arithmetic a => [Integer] -> Constraint a -> Integer
toVar srcs c = fromBinary $ castBits $ binaryExpansion ex
    where
        r  = toZp 903489679376934896793395274328947923579382759823 :: Zp VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: Zp VarField
        v  = BinScale @a . (+ r) . toZp
        x  = g ^ runBinScale (v `evalPolynomial` c)
        ex = foldr (\p y -> x ^ p + y) x srcs

newVariableWithSource :: Arithmetic a => [Integer] -> (Integer -> Constraint a) -> State (ArithmeticCircuit a) Integer
newVariableWithSource srcs con = toVar srcs . con . fst <$> do
    zoom #acRNG $ get >>= traverse put . randomR (0, order @VarField - 1)

addVariable :: Integer -> State (ArithmeticCircuit a) Integer
addVariable x = do
    zoom #acOutput $ put x
    zoom #acVarOrder . modify
        $ insert <$> (,x) . length <*> const x <*> id
    pure x

---------------------------------- Low-level functions --------------------------------

type ConstraintMonomial = SomeMonomial

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint a = SomePolynomial a

-- | Adds a constraint to the arithmetic circuit.
constraint :: Arithmetic a => Constraint a -> State (ArithmeticCircuit a) ()
constraint c = zoom #acSystem . modify $ insert (toVar [] c) c

-- | Forces the current variable to be zero.
forceZero :: forall a . Arithmetic a => State (ArithmeticCircuit a) ()
forceZero = zoom #acOutput get >>= constraint . var

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: (Map Integer a -> a) -> State (ArithmeticCircuit a) ()
assignment f = do
    i <- insert <$> zoom #acOutput get
    zoom #acWitness . modify $ (.) (f >>= i)

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
eval :: ArithmeticCircuit a -> Map Integer a -> a
eval ctx i = acWitness ctx i ! acOutput ctx

-- | Applies the values of the first `n` inputs to the arithmetic circuit.
-- TODO: make this safe
apply :: [a] -> State (ArithmeticCircuit a) ()
apply xs = do
    inputs <- zoom #acInput get
    zoom #acInput . put $ drop (length xs) inputs
    zoom #acWitness . modify $ (. (union . fromList $ zip inputs xs))

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
