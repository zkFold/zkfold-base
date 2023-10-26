{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Protocol.Arithmetization.R1CS (
        BigField,
        Arithmetizable(..),
        R1CS,
        -- high-level functions
        applyArgs,
        compile,
        optimize,
        -- information about the system
        r1csSizeN,
        r1csSizeM,
        r1csSystem,
        r1csValue,
        r1csPrint,
        -- R1CS type fields
        r1csVarOrder,
        r1csOutput
    ) where

import           Control.Monad.State                  (MonadState (..), State, modify, execState, evalState)
import           Data.Bool                            (bool)
import           Data.List                            (nub)
import           Data.Map                             hiding (take, drop, foldl, null, map, foldr)
import           Prelude                              hiding (Num (..), (^), sum, take, drop, product, length)
import qualified Prelude                              as Haskell
import           System.Random                        (StdGen, Random (..), mkStdGen, uniform)
import           Text.Pretty.Simple                   (pPrint)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Data.PartialOrder      (mergeMaps)
import           ZkFold.Prelude                       (length, drop, take)

-- | A class for arithmetizable types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the type to be arithmetized.
class (FiniteField a, Eq a, ToBits a) => Arithmetizable a x where
    -- | Arithmetizes `x`, adds it to the current circuit, and returns the outputs that make up `x`.
    arithmetize :: x -> State (R1CS a) [R1CS a]

    -- | Restores `x` from outputs from the circuits' outputs.
    restore :: [R1CS a] -> x

    -- | Returns the number of finite field elements needed to desscribe `x`.
    typeSize :: Integer

instance (Arithmetizable a x, Arithmetizable a y) => Arithmetizable a (x, y) where
    arithmetize (a, b) = do
        x <- arithmetize a
        y <- arithmetize b
        return $ x ++ y

    -- TODO: this should work with objects of arbitrary sizes.
    restore [r1, r2] = (restore [r1], restore [r2])
    restore _        = error "restore: wrong number of arguments"

    typeSize = typeSize @a @x + typeSize @a @y

instance Arithmetizable a x => Arithmetizable a [x] where
    arithmetize []     = return []
    arithmetize (a:as) = do
        x <- arithmetize a
        (x ++) <$> arithmetize as

    -- TODO: this should work with objects of arbitrary sizes.
    restore rs = map (\r -> restore [r]) rs

    typeSize = typeSize @a @x

instance (Arithmetizable a x, Arithmetizable a f) => Arithmetizable a (x -> f) where
    arithmetize f = do
        x <- mapM (const input) [1..typeSize @a @x]
        arithmetize (f $ restore x)

    restore = error "restore: not implemented"

    typeSize = 1 + typeSize @a @f

-- | A rank-1 constraint system (R1CS).
-- This type represents the result of compilation of a function into a R1CS.
data R1CS a = R1CS
    {
        r1csMatrices :: Map Integer (Map Integer a, Map Integer a, Map Integer a),
        -- ^ The R1CS matrices
        r1csInput    :: [Integer],
        -- ^ The input variables
        r1csWitness  :: Map Integer a -> Map Integer a,
        -- ^ The witness generation function
        r1csOutput   :: Integer,
        -- ^ The output variable
        r1csVarOrder :: Map Integer Integer,
        -- ^ The order of variable assignments
        r1csRNG      :: StdGen
    }

--------------------------------- High-level functions --------------------------------

-- TODO: make this work for different input types.
applyArgs :: forall a . R1CS a -> [a] -> R1CS a
applyArgs r args = execState (apply args) r

-- | Compiles function `f` into a R1CS.
compile :: forall a f y . (Arithmetizable a f, Arithmetizable a y) => f -> y
compile f = restore @a $ evalState (arithmetize f) mempty

-- | Optimizes the constraint system.
--
-- TODO: Implement this.
optimize :: R1CS a -> R1CS a
optimize = undefined

---------------------------------- Low-level functions --------------------------------

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint a = (Map Integer a, Map Integer a, Map Integer a)

-- | Adds a constraint to the arithmetic circuit.
constraint :: Constraint a -> State (R1CS a) ()
constraint con = modify $ \r -> r { r1csMatrices = insert (r1csSizeN r) con (r1csMatrices r) }

-- | Forces the current variable to be zero.
forceZero :: forall a . FiniteField a => State (R1CS a) ()
forceZero = do
    r <- get
    let x   = r1csOutput r
        con = (empty, empty, singleton x one)
    constraint con

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: forall a . (Map Integer a -> a) -> State (R1CS a) ()
assignment f = modify $ \r -> r { r1csWitness = \i -> insert (r1csOutput r) (f i) (r1csWitness r i) }

-- | Adds a new input variable to the arithmetic circuit. Returns a copy of the arithmetic circuit with this variable as output.
input :: forall a . State (R1CS a) (R1CS a)
input = modify (\(r :: R1CS a) ->
        let ins = r1csInput r
            s   = if null ins then 1 else maximum (r1csInput r) + 1
        in r
        {
            r1csInput    = ins ++ [s],
            r1csOutput   = s,
            r1csVarOrder = insert (length $ r1csVarOrder r) s (r1csVarOrder r)
        }) >> get

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: R1CS a -> Map Integer a -> a
eval ctx i =
    let w = r1csWitness ctx i
        o = r1csOutput ctx
    in w ! o

-- | Applies the values of the first `n` inputs to the arithmetic circuit.
-- TODO: make this safe
apply :: [a] -> State (R1CS a) ()
apply xs = modify (\(r :: R1CS a) ->
    let ins = r1csInput r
        n   = length xs
    in r
    {
        r1csInput = drop n ins,
        r1csWitness = r1csWitness r . (fromList (zip (take n ins) xs) `union`)
    })

------------------------------------- Instances -------------------------------------

instance Eq a => Semigroup (R1CS a) where
    r1 <> r2 = R1CS
        {
            r1csMatrices =
                let m1 = elems $ r1csMatrices r1
                    m2 = elems $ r1csMatrices r2
                in fromList $ zip [0..] $ nub (m1 ++ m2),
            -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
            -- We need a way to ensure the correct order no matter how `(<>)` is used.
            r1csInput    = nub $ r1csInput r1 ++ r1csInput r2,
            r1csWitness  = \w -> r1csWitness r1 w `union` r1csWitness r2 w,
            r1csOutput   = r1csOutput r1,
            r1csVarOrder = mergeMaps (r1csVarOrder r1) (r1csVarOrder r2),
            r1csRNG      = mkStdGen $ fst (uniform (r1csRNG r1)) Haskell.* fst (uniform (r1csRNG r2))
        }

instance (FiniteField a, Eq a) => Monoid (R1CS a) where
    mempty = R1CS
        {
            r1csMatrices = empty,
            r1csInput    = [],
            r1csWitness  = insert 0 one,
            r1csOutput   = 0,
            r1csVarOrder = empty,
            r1csRNG      = mkStdGen 0
        }

instance (FiniteField a, Eq a, ToBits a) =>
        Arithmetizable a (R1CS a) where
    arithmetize r = do
        r' <- get
        put $ r <> r'
        return [r <> r']

    restore [r] = r
    restore _   = error "restore: wrong number of arguments"

    typeSize = 1

instance FiniteField a => Finite (R1CS a) where
    order = order @a

instance (FiniteField a, Eq a, ToBits a) => AdditiveSemigroup (R1CS a) where
    r1 + r2 = flip execState (r1 <> r2) $ do
        let x1  = r1csOutput r1
            x2  = r1csOutput r2
            con = \z -> (empty, empty, fromListWith (+) [(x1, one), (x2, one), (z, negate one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (eval r1 + eval r2)

instance (FiniteField a, Eq a, ToBits a) => AdditiveMonoid (R1CS a) where
    zero = flip execState mempty $ do
        let con = \z -> (empty, empty, fromList [(z, one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment zero

instance (FiniteField a, Eq a, ToBits a) => AdditiveGroup (R1CS a) where
    negate r = flip execState r $ do
        let x   = r1csOutput r
            con = \z -> (empty, empty, fromList [(x, one), (z, one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (negate $ eval r)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeSemigroup (R1CS a) where
    r1 * r2 = flip execState (r1 <> r2) $ do
        let x1  = r1csOutput r1
            x2  = r1csOutput r2
            con = \z -> (singleton x1 one, singleton x2 one, singleton z one)
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (eval r1 * eval r2)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeMonoid (R1CS a) where
    one = mempty

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeGroup (R1CS a) where
    invert r = flip execState r $ do
        let x    = r1csOutput r
            con  = \y -> (singleton x one, singleton y one, empty)
        y <- newVariableFromConstraint con
        addVariable y
        constraint $ con y
        assignment (bool zero one . (== zero) . eval r )
        let con' = \z -> (singleton x one, singleton z one, fromList [(0, one), (y, negate one)])
        z <- newVariableFromConstraint con'
        addVariable z
        constraint $ con' z
        assignment (invert $ eval r)

instance (FiniteField a, Eq a, ToBits a, FromConstant b a) => FromConstant b (R1CS a) where
    fromConstant c = flip execState mempty $ do
        let x = fromConstant c
            con = \z -> (empty, empty, fromList [(0, x), (z, negate one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (const x)

instance (FiniteField a, Eq a, ToBits a) => ToBits (R1CS a) where
    toBits x =
        let two = one + one
            ps  = map (two ^) [0.. numberOfBits @a - 1]
            f z = flip evalState z $ mapM (const $ do
                    x' <- newVariable
                    addVariable x'
                    get
                ) [0.. numberOfBits @a - 1]
            v z = z - sum (zipWith (*) (f z) ps)
            y   = x { r1csRNG = r1csRNG (v x) }
            bs  = map r1csOutput $ f y
            r   = execState forceZero $ v y
        in map (\x'' -> r { r1csOutput = x'' } ) bs

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
r1csSizeN :: R1CS a -> Integer
r1csSizeN = length . r1csMatrices

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
r1csSizeM :: R1CS a -> Integer
r1csSizeM = length . r1csVarOrder

r1csSystem :: R1CS a -> Map Integer (Map Integer a, Map Integer a, Map Integer a)
r1csSystem = r1csMatrices

r1csValue :: R1CS a -> a
r1csValue r = eval r mempty

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere.
-- TODO: Check that all arguments have been applied.
r1csPrint :: forall a . Show a => R1CS a -> IO ()
r1csPrint r = do
    let m = elems (r1csSystem r)
        i = r1csInput r
        w = r1csWitness r empty
        o = r1csOutput r
        v = r1csValue r
        vo = r1csVarOrder r
    putStr "System size: "
    pPrint $ r1csSizeN r
    putStr "Variable size: "
    pPrint $ r1csSizeM r
    putStr "Matrices: "
    pPrint m
    putStr "Input: "
    pPrint i
    putStr "Witness: "
    pPrint w
    putStr "Variable order: "
    pPrint vo
    putStr "Output: "
    pPrint o
    putStr "Value: "
    pPrint v

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the R1CS compiler for generating new variable indices.
--
-- TODO: move this elsewhere
data BigField
instance Finite BigField where
    order = 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance Prime BigField

-- -- TODO: Remove the hardcoded constant.
con2var :: (Eq a, ToBits a) => (Map Integer a, Map Integer a, Map Integer a) -> Integer
con2var (a, b, c) = g a + g b + g c
    where
        z         = toZp 891752917250912079751095709127490 :: Zp BigField
        f (x, y)  = multiExp z (map (toZp :: Integer -> Zp BigField) x) + multiExp z y
        g m       = fromZp $ f $ unzip $ toList m

newVariable :: State (R1CS a) Integer
newVariable = do
    r <- get
    let (x, g) = randomR (0, order @BigField - 1) (r1csRNG r)
    put r { r1csRNG = g }
    return x

newVariableFromConstraint :: (Eq a, ToBits a) => (Integer -> Constraint a) -> State (R1CS a) Integer
newVariableFromConstraint con = con2var . con <$> newVariable

-- newVariableFromVariable :: Integer -> State (R1CS a) Integer
-- newVariableFromVariable x = fromZp . toZp @BigField . (x *)  <$> newVariable

addVariable :: Integer -> State (R1CS a) ()
addVariable x = modify (\r -> r { r1csOutput = x, r1csVarOrder = r1csVarOrder r `union` singleton (length (r1csVarOrder r)) x })