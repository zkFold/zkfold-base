{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Arithmetization (
        BigField,
        Arithmetizable(..),
        ArithmeticCircuit,
        -- high-level functions
        applyArgs,
        optimize,
        -- information about the system
        acSizeN,
        acSizeM,
        acSystem,
        acValue,
        acPrint,
        -- R1CS type fields
        acVarOrder,
        acOutput
    ) where

import           Control.Monad.State             (MonadState (..), State, modify, execState, evalState)
import           Data.Aeson
import           Data.Bool                       (bool)
import           Data.List                       (nub)
import           Data.Map                        hiding (take, drop, splitAt, foldl, null, map, foldr)
import           Prelude                         hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)
import qualified Prelude                         as Haskell
import           System.Random                   (StdGen, Random (..), mkStdGen, uniform)
import           Text.Pretty.Simple              (pPrint)
import           Type.Data.Num.Unary             (Natural)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Prelude                  ((!!), length, drop, take, splitAt)
import           ZkFold.Symbolic.Data.List       (List, mapList, lengthList, indicesInteger)

-- | A class for arithmetizable types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the type to be arithmetized.
class (FiniteField a, Eq a, ToBits a) => Arithmetizable a x where
    -- | Arithmetizes `x`, adds it to the current circuit, and returns the outputs that make up `x`.
    arithmetize :: x -> State (ArithmeticCircuit a) [ArithmeticCircuit a]

    -- | Restores `x` from outputs from the circuits' outputs.
    restore :: [ArithmeticCircuit a] -> x

    -- | Returns the number of finite field elements needed to desscribe `x`.
    typeSize :: Integer

instance (Arithmetizable a x, Arithmetizable a y) => Arithmetizable a (x, y) where
    arithmetize (a, b) = do
        x <- arithmetize a
        y <- arithmetize b
        return $ x ++ y

    restore rs
        | length rs /= typeSize @a @(x, y) = error "restore: wrong number of arguments"
        | otherwise = (restore rsX, restore rsY)
        where (rsX, rsY) = splitAt (typeSize @a @x) rs 

    typeSize = typeSize @a @x + typeSize @a @y

instance (Arithmetizable a x, Natural n) => Arithmetizable a (List n x) where
    arithmetize xs = concat <$> mapM arithmetize xs

    restore rs
        | length rs /= typeSize @a @(List n x) = error "restore: wrong number of arguments"
        | otherwise = mapList (f rs) indicesInteger
        where
            f :: [ArithmeticCircuit a] -> Integer -> x
            f as = restore @a @x . take (lengthList @n) . flip drop as . ((lengthList @n) *)

    typeSize = typeSize @a @x * (lengthList @n)

instance (Arithmetizable a x, Arithmetizable a f) => Arithmetizable a (x -> f) where
    arithmetize f = do
        x <- mapM (const input) [1..typeSize @a @x]
        arithmetize (f $ restore x)

    restore = error "restore: not implemented"

    typeSize = error "typeSize: not implemented"

-- | Arithmetic circuit in the form of a rank-1 constraint system (R1CS).
-- This type represents the result of compilation of a function into a R1CS.
data ArithmeticCircuit a = ArithmeticCircuit
    {
        acMatrices :: Map Integer (Map Integer a, Map Integer a, Map Integer a),
        -- ^ The R1CS matrices
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

--------------------------------- High-level functions --------------------------------

-- TODO: make this work for different input types.
applyArgs :: forall a . ArithmeticCircuit a -> [a] -> ArithmeticCircuit a
applyArgs r args = execState (apply args) r

-- | Optimizes the constraint system.
--
-- TODO: Implement this.
optimize :: ArithmeticCircuit a -> ArithmeticCircuit a
optimize = undefined

---------------------------------- Low-level functions --------------------------------

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint a = (Map Integer a, Map Integer a, Map Integer a)

-- | Adds a constraint to the arithmetic circuit.
constraint :: (Eq a, ToBits a) => Constraint a -> State (ArithmeticCircuit a) ()
constraint con = modify $ \r -> r { acMatrices = insert (con2var con) con (acMatrices r) }

-- | Forces the current variable to be zero.
forceZero :: forall a . (FiniteField a, Eq a, ToBits a) => State (ArithmeticCircuit a) ()
forceZero = do
    r <- get
    let x   = acOutput r
        con = (empty, empty, singleton x one)
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

------------------------------------- Instances -------------------------------------

instance Eq a => Semigroup (ArithmeticCircuit a) where
    r1 <> r2 = ArithmeticCircuit
        {
            acMatrices = acMatrices r1 `union` acMatrices r2,
            -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
            -- We need a way to ensure the correct order no matter how `(<>)` is used.
            acInput    = nub $ acInput r1 ++ acInput r2,
            acWitness  = \w -> acWitness r1 w `union` acWitness r2 w,
            acOutput   = max (acOutput r1) (acOutput r2),
            acVarOrder = acVarOrder r1 `union` acVarOrder r2,
            acRNG      = mkStdGen $ fst (uniform (acRNG r1)) Haskell.* fst (uniform (acRNG r2))
        }

instance (FiniteField a, Eq a) => Monoid (ArithmeticCircuit a) where
    mempty = ArithmeticCircuit
        {
            acMatrices = empty,
            acInput    = [],
            acWitness  = insert 0 one,
            acOutput   = 0,
            acVarOrder = empty,
            acRNG      = mkStdGen 0
        }

instance (FiniteField a, Eq a, ToBits a) => Arithmetizable a (ArithmeticCircuit a) where
    arithmetize r = do
        r' <- get
        let r'' = r <> r' { acOutput = acOutput r }
        put r''
        return [r'']

    restore [r] = r
    restore _   = error "restore: wrong number of arguments"

    typeSize = 1

instance FiniteField a => Finite (ArithmeticCircuit a) where
    order = order @a

instance (FiniteField a, Eq a, ToBits a) => AdditiveSemigroup (ArithmeticCircuit a) where
    r1 + r2 = flip execState (r1 <> r2) $ do
        let x1  = acOutput r1
            x2  = acOutput r2
            con = \z -> (empty, empty, fromListWith (+) [(x1, one), (x2, one), (z, negate one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (eval r1 + eval r2)

instance (FiniteField a, Eq a, ToBits a) => AdditiveMonoid (ArithmeticCircuit a) where
    zero = flip execState mempty $ do
        let con = \z -> (empty, empty, fromList [(z, one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment zero

instance (FiniteField a, Eq a, ToBits a) => AdditiveGroup (ArithmeticCircuit a) where
    negate r = flip execState r $ do
        let x   = acOutput r
            con = \z -> (empty, empty, fromList [(x, one), (z, one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (negate $ eval r)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeSemigroup (ArithmeticCircuit a) where
    r1 * r2 = flip execState (r1 <> r2) $ do
        let x1  = acOutput r1
            x2  = acOutput r2
            con = \z -> (singleton x1 one, singleton x2 one, singleton z one)
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (eval r1 * eval r2)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeMonoid (ArithmeticCircuit a) where
    one = mempty

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeGroup (ArithmeticCircuit a) where
    invert r = flip execState r $ do
        let x    = acOutput r
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

instance (FiniteField a, Eq a, ToBits a, FromConstant b a) => FromConstant b (ArithmeticCircuit a) where
    fromConstant c = flip execState mempty $ do
        let x = fromConstant c
            con = \z -> (empty, empty, fromList [(0, x), (z, negate one)])
        z <- newVariableFromConstraint con
        addVariable z
        constraint $ con z
        assignment (const x)

instance (FiniteField a, Eq a, ToBits a) => ToBits (ArithmeticCircuit a) where
    toBits x =
        let two = one + one
            ps  = map (two ^) [0.. numberOfBits @a - 1]
            f z = flip evalState z $ mapM (\i -> do
                    x' <- newVariable
                    addVariable x'
                    assignment ((!! i) . padBits (numberOfBits @a) . toBits . eval x)
                    constraint (singleton x' one, fromList [(0, one), (x', negate one)], empty)
                    get
                ) [0.. numberOfBits @a - 1]
            v z = z - sum (zipWith (*) (f z) ps)
            y   = x { acRNG = acRNG (v x) }
            bs  = map acOutput $ f y
            r   = execState forceZero $ v y
        in map (\x'' -> r { acOutput = x'' } ) bs

-- TODO: add witness generation info to the JSON object
instance ToJSON a => ToJSON (ArithmeticCircuit a) where
    toJSON r = object
        [
            "matrices" .= acMatrices r,
            "input"    .= acInput r,
            "output"   .= acOutput r,
            "order"    .= acVarOrder r
        ]

-- TODO: properly restore the witness generation function
instance FromJSON a => FromJSON (ArithmeticCircuit a) where
    parseJSON = withObject "ArithmeticCircuit" $ \v -> ArithmeticCircuit
        <$> v .: "matrices"
        <*> v .: "input"
        <*> pure (const empty)
        <*> v .: "output"
        <*> v .: "order"
        <*> pure (mkStdGen 0)

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a -> Integer
acSizeN = length . acMatrices

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
acSizeM :: ArithmeticCircuit a -> Integer
acSizeM = length . acVarOrder

acSystem :: ArithmeticCircuit a -> Map Integer (Map Integer a, Map Integer a, Map Integer a)
acSystem = acMatrices

acValue :: ArithmeticCircuit a -> a
acValue r = eval r mempty

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere.
-- TODO: Check that all arguments have been applied.
acPrint :: forall a . Show a => ArithmeticCircuit a -> IO ()
acPrint r = do
    let m = elems (acSystem r)
        i = acInput r
        w = acWitness r empty
        o = acOutput r
        v = acValue r
        vo = acVarOrder r
    putStr "System size: "
    pPrint $ acSizeN r
    putStr "Variable size: "
    pPrint $ acSizeM r
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

-- TODO: Remove the hardcoded constant.
con2var :: (Eq a, ToBits a) => (Map Integer a, Map Integer a, Map Integer a) -> Integer
con2var (a, b, c) = g a + g b + g c
    where
        z         = toZp 891752917250912079751095709127490 :: Zp BigField
        f (x, y)  = multiExp z (map (toZp :: Integer -> Zp BigField) x) + multiExp z y
        g m       = fromZp $ f $ unzip $ toList m

newVariable :: State (ArithmeticCircuit a) Integer
newVariable = do
    r <- get
    let (x, g) = randomR (0, order @BigField - 1) (acRNG r)
    put r { acRNG = g }
    return x

newVariableFromConstraint :: (Eq a, ToBits a) => (Integer -> Constraint a) -> State (ArithmeticCircuit a) Integer
newVariableFromConstraint con = con2var . con <$> newVariable

-- newVariableFromVariable :: Integer -> State (R1CS a) Integer
-- newVariableFromVariable x = fromZp . toZp @BigField . (x *)  <$> newVariable

addVariable :: Integer -> State (ArithmeticCircuit a) ()
addVariable x = modify (\r -> r { acOutput = x, acVarOrder = insert (length (acVarOrder r), x) x (acVarOrder r)})