{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Protocol.Arithmetization.R1CS (
        BigField,
        R1CS,
        r1csSizeN,
        r1csSizeM,
        r1csOptimize,
        r1csValue,
        r1csPrint
    ) where

import           Control.Monad.State                  (MonadState (..), modify, execState, gets)
import           Data.List                            (nub)
import           Data.Map                             hiding (take, drop, foldl, null, map, foldr)
import           Prelude                              hiding (Num (..), (^), take, drop, product, length)
import           Text.Pretty.Simple                   (pPrint)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Data.Conditional       (bool)
import           ZkFold.Crypto.Data.Symbolic          (Symbolic (..), SymbolicVariable (..))
import           ZkFold.Prelude                       (length, drop, take)

-- | A finite field with a large order.
-- It is used in the R1CS compiler for generating new variable indices.
--
-- TODO: move this elsewhere
data BigField
instance Finite BigField where
    order = 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance Prime BigField

-- | A rank-1 constraint system (R1CS).
-- This type represents the result of a compilation of a function into a R1CS.
--
-- To compile a function @/f :: C a => a -> a/@, we must define an instance @/C (R1CS a)/@.
-- Keep in mind that the more type constraints we impose on the polymorphic argument @/a/@,
-- the broader the class of functions that can be compiled.
data R1CS a t = R1CS
    {
        r1csMatrices :: Map Integer (Map Integer a, Map Integer a, Map Integer a),
        -- ^ The R1CS matrices
        r1csInput    :: [Integer],
        -- ^ The input variables
        r1csWitness  :: Map Integer a -> Map Integer a,
        -- ^ The witness generation function
        r1csOutput   :: [Integer]
        -- ^ The output variable
    }

-- | Calculates the number of constraints in the system.
r1csSizeN :: R1CS a t -> Integer
r1csSizeN = length . r1csMatrices

-- | Calculates the number of variables in the system.
r1csSizeM :: R1CS a t -> Integer
r1csSizeM r = length $ nub $ concatMap (keys . f) (elems $ r1csMatrices r)
    where f (a, b, c) = a `union` b `union` c

-- | Optimizes the constraint system.
--
-- TODO: Implement this.
r1csOptimize :: R1CS a t -> R1CS a t
r1csOptimize = undefined

r1csValue :: forall a t . (FiniteField a, Eq a, ToBits a, SymbolicVariable a t) => R1CS a t -> t
r1csValue r = eval @(R1CS a t) @(R1CS a t) r mempty

-- | Prints the constraint system, the witness, and the output on a given input.
--
-- TODO: Move this elsewhere.
r1csPrint :: forall a t . (FiniteField a, Eq a, ToBits a, SymbolicVariable a t, Show a, Show t) => R1CS a t -> IO ()
r1csPrint r = do
    let m = elems (r1csMatrices r)
        i = r1csInput r
        w = r1csWitness r empty
        o = r1csOutput r
        v = r1csValue r
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
    putStr "Output: "
    pPrint o
    putStr"Value: "
    pPrint v

------------------------------------- Instances -------------------------------------

instance Eq a => Semigroup (R1CS a t) where
    -- The concatenation is left-biased.
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
            r1csOutput   = r1csOutput r1
        }

instance (FiniteField a, Eq a) => Monoid (R1CS a t) where
    mempty = R1CS
        {
            r1csMatrices = empty,
            r1csInput    = [],
            r1csWitness  = insert 0 one,
            r1csOutput   = []
        }

instance (FiniteField a, Eq a, ToBits a, SymbolicVariable a t) => Symbolic (R1CS a t) (R1CS a t) where
    type ValueOf (R1CS a t) = t

    type InputOf (R1CS a t) = Map Integer a

    type Constraint (R1CS a t) (R1CS a t) = [Integer -> (Map Integer a, Map Integer a, Map Integer a)]

    merge r = do
        r' <- get
        let r'' = r <> r'
        put r''
        return [r'']

    -- TODO: add check that `length vars == symbolSize @a @t`
    constraint cons = do
        r0 <- get
        let (r1, vars) = foldl (\(r, xs) con ->
                let x = r1csNewVariable (con $ -1)
                in (r { r1csMatrices = insert (r1csSizeN r) (con x) (r1csMatrices r)}, xs ++ [x]))
                (r0, []) cons
        put $ r1 { r1csOutput = vars }

    -- TODO: forbid reassignment of variables
    -- TODO: add check that `length (r1csOutput r) == symbolSize @a @t
    assignment f = modify $ \r -> r
        {
            r1csWitness = \i -> fromList (zip (r1csOutput r) (fromValue $ f i)) `union` r1csWitness r i
        }

    input = modify (\r ->
        let ins = r1csInput r
            s   = if null ins then 1 else maximum (r1csInput r) + 1
        in r
        {
            r1csInput  = ins ++ [s..s + symbolSize @a @t - 1],
            r1csOutput = [s..s + symbolSize @a @t - 1]
        }) >> get

    current = get

    -- TODO: make this safe
    apply x = modify (\r ->
        let ins = r1csInput r
            n   = symbolSize @a @t
        in r
        {
            r1csInput = drop n ins,
            r1csWitness = r1csWitness r . (fromList (zip (take n ins) (fromValue x)) `union`)
        })

    eval ctx = \i ->
        let w = r1csWitness ctx i
            o = r1csOutput ctx
        in toValue $ map (w !) o

instance (FiniteField a) => Finite (R1CS a a) where
    order = order @a

instance (FiniteField a, Eq a, ToBits a) => AdditiveSemigroup (R1CS a a) where
    r1 + r2 = flip execState (r1 <> r2) $ do
        let con = \z -> (empty, empty, fromListWith (+) [(head $ r1csOutput r1, one), (head $ r1csOutput r2, one), (z, negate one)])
        constraint @(R1CS a a) @(R1CS a a) [con]
        assignment @(R1CS a a) @(R1CS a a) (eval @(R1CS a a) @(R1CS a a) r1 + eval @(R1CS a a) @(R1CS a a) r2)

instance (FiniteField a, Eq a, ToBits a) => AdditiveMonoid (R1CS a a) where
    zero = flip execState mempty $ do
        let con = \z -> (empty, empty, fromList [(z, one)])
        constraint @(R1CS a a) @(R1CS a a) [con]
        assignment @(R1CS a a) @(R1CS a a) zero

instance (FiniteField a, Eq a, ToBits a) => AdditiveGroup (R1CS a a) where
    negate r = flip execState r $ do
        let con = \z -> (empty, empty, fromList [(head $ r1csOutput r, one), (z, one)])
        constraint @(R1CS a a) @(R1CS a a) [con]
        assignment @(R1CS a a) @(R1CS a a) (negate . eval @(R1CS a a) @(R1CS a a) r)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeSemigroup (R1CS a a) where
    r1 * r2 = flip execState (r1 <> r2) $ do
        let con = \z -> (singleton (head $ r1csOutput r1) one, singleton (head $ r1csOutput r2) one, singleton z one)
        constraint @(R1CS a a) @(R1CS a a) [con]
        assignment @(R1CS a a) @(R1CS a a) (eval @(R1CS a a) @(R1CS a a) r1 * eval @(R1CS a a) @(R1CS a a) r2)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeMonoid (R1CS a a) where
    one = mempty { r1csOutput = [0] }

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeGroup (R1CS a a) where
    invert r = flip execState r $ do
        let con  = \z -> (singleton (head $ r1csOutput r) one, singleton z one, empty)
        constraint @(R1CS a a) @(R1CS a a) [con]
        assignment @(R1CS a a) @(R1CS a a) (bool zero one . (== zero) . eval @(R1CS a a) @(R1CS a a) r)
        y  <- gets (head . r1csOutput)
        let con' = \z -> (singleton (head $ r1csOutput r) one, singleton z one, fromList [(0, one), (y, negate one)])
        constraint @(R1CS a a) @(R1CS a a) [con']
        assignment @(R1CS a a) @(R1CS a a) (invert . eval @(R1CS a a) @(R1CS a a) r)

instance (FiniteField a, Eq a, ToBits a, FromConstant b a) => FromConstant b (R1CS a a) where
    fromConstant c = flip execState mempty $ do
        let x = fromConstant c
            con = \z -> (empty, empty, fromList [(0, x), (z, negate one)])
        constraint @(R1CS a a) @(R1CS a a) [con]
        assignment @(R1CS a a) @(R1CS a a) (const x)

------------------------------------- Internal -------------------------------------

-- TODO: Remove the hardcoded constant.
r1csNewVariable :: (Eq a, ToBits a) => (Map Integer a, Map Integer a, Map Integer a) -> Integer
r1csNewVariable (a, b, c) = g a + g b + g c
    where
        z         = toZp 891752917250912079751095709127490 :: Zp BigField
        f (x, y)  = multiExp z (map (toZp :: Integer -> Zp BigField) x) + multiExp z y
        g m       = fromZp $ f $ unzip $ toList m