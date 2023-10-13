{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Protocol.Arithmetization.R1CS (
        BigField,
        R1CS,
        r1csSizeN,
        r1csSizeM,
        r1csSystem,
        r1csVarOrder,
        r1csOutput,
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
import           ZkFold.Crypto.Data.Arithmetization   (Arithmetization (..))
import           ZkFold.Crypto.Data.Conditional       (bool)
import           ZkFold.Crypto.Data.Ord               (mergeMaps)
import           ZkFold.Crypto.Data.Symbolic          (Symbolic (..))
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
-- To compile a function @/f :: C t => t -> t/@, we must define an instance @/C (R1CS a t s)/@.
-- Keep in mind that the more type constraints we impose on the polymorphic argument @/t/@,
-- the broader the class of functions that can be compiled.
data R1CS a t s = R1CS
    {
        r1csMatrices :: Map Integer (Map Integer a, Map Integer a, Map Integer a),
        -- ^ The R1CS matrices
        r1csInput    :: [Integer],
        -- ^ The input variables
        r1csWitness  :: Map Integer a -> Map Integer a,
        -- ^ The witness generation function
        r1csOutput   :: [Integer],
        -- ^ The output variable
        r1csVarOrder :: Map Integer Integer
        -- ^ The order of variable assignments
    }

-- | Calculates the number of constraints in the system.
r1csSizeN :: R1CS a t s -> Integer
r1csSizeN = length . r1csMatrices

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
r1csSizeM :: R1CS a t s -> Integer
r1csSizeM = length . r1csVarOrder

r1csSystem :: R1CS a t s -> Map Integer (Map Integer a, Map Integer a, Map Integer a)
r1csSystem = r1csMatrices

-- | Optimizes the constraint system.
--
-- TODO: Implement this.
r1csOptimize :: R1CS a t s -> R1CS a t s
r1csOptimize = undefined

r1csValue :: forall a t s . (FiniteField a, Eq a, ToBits a, Symbolic a t s) => R1CS a t s -> t
r1csValue r = eval @(R1CS a t s) @(R1CS a t s) r mempty

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere.
-- TODO: Check that all arguments have been applied.
r1csPrint :: forall a t s . (FiniteField a, Eq a, ToBits a, Symbolic a t s, Show a, Show t) => R1CS a t s -> IO ()
r1csPrint r = do
    let m = elems (r1csMatrices r)
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
    putStr"Value: "
    pPrint v

------------------------------------- Instances -------------------------------------

instance Eq a => Semigroup (R1CS a t s) where
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
            r1csOutput   = r1csOutput r1 ++ r1csOutput r2,
            r1csVarOrder = mergeMaps (r1csVarOrder r1) (r1csVarOrder r2)
        }

instance (FiniteField a, Eq a) => Monoid (R1CS a t s) where
    mempty = R1CS
        {
            r1csMatrices = empty,
            r1csInput    = [],
            r1csWitness  = insert 0 one,
            r1csOutput   = [],
            r1csVarOrder = empty
        }

instance (FiniteField a, Eq a, ToBits a, Symbolic a t s) => Arithmetization (R1CS a t s) (R1CS a t s) where
    type ValueOf (R1CS a t s) = t

    type InputOf (R1CS a t s) = Map Integer a

    type Constraint (R1CS a t s) (R1CS a t s) = [Integer -> (Map Integer a, Map Integer a, Map Integer a)]

    -- `merge` is a concatenation that sets its argument as the output.
    merge r = do
        r' <- get
        let r'' = (r <> r') { r1csOutput = r1csOutput r} :: R1CS a t s
        put r''

    atomic r = map (\x -> r { r1csOutput = [x] }) $ r1csOutput r

    -- TODO: add check that `length vars == symbolSize @a @t`
    constraint cons = do
        (r0 :: R1CS a t s) <- get
        let (r1, vars) = foldl (\(r, xs) con ->
                let x = r1csNewVariable (con $ -1)
                in (r { r1csMatrices = insert (r1csSizeN r) (con x) (r1csMatrices r)}, xs ++ [x]))
                (r0, []) cons
        put (r1 { r1csOutput = vars, r1csVarOrder = r1csVarOrder r1 `union` fromList (zip [length (r1csVarOrder r1)..] vars) } :: R1CS a t s)

    -- TODO: forbid reassignment of variables
    -- TODO: add check that `length (r1csOutput r) == symbolSize @a @t`
    assignment f = modify $ \r -> r
        {
            r1csWitness = \i -> fromList (zip (r1csOutput r) (fromValue @a @t @s $ f i)) `union` r1csWitness r i
        } :: R1CS a t s

    input = modify (\(r :: R1CS a t s) ->
        let ins = r1csInput r
            s   = if null ins then 1 else maximum (r1csInput r) + 1
            insNew = [s..s + symbolSize @a @t @s - 1]
        in r
        {
            r1csInput    = ins ++ insNew,
            r1csOutput   = insNew,
            r1csVarOrder = r1csVarOrder r `union` fromList (zip [length (r1csVarOrder r)..] insNew)
        }) >> get

    -- TODO: add check that `length (r1csOutput r) == symbolSize @a @t`
    current = get

    -- TODO: make this safe
    apply x = modify (\(r :: R1CS a t s) ->
        let ins = r1csInput r
            n   = symbolSize @a @t @s
        in r
        {
            r1csInput = drop n ins,
            r1csWitness = r1csWitness r . (fromList (zip (take n ins) (fromValue @a @t @s x)) `union`)
        })

    eval ctx = \i ->
        let w = r1csWitness ctx i
            o = r1csOutput ctx
        in toValue @a @t @s $ map (w !) o

type R a = R1CS a a Integer

instance (FiniteField a) => Finite (R a) where
    order = order @a

instance (FiniteField a, Eq a, ToBits a) => AdditiveSemigroup (R a) where
    r1 + r2 = flip execState (r1 <> r2) $ do
        let x1  = toSymbol @a @a $ r1csOutput r1
            x2  = toSymbol @a @a $ r1csOutput r2
            con = \z -> (empty, empty, fromListWith (+) [(x1, one), (x2, one), (z, negate one)])
        constraint @(R a) @(R a) [con]
        assignment @(R a) @(R a) (eval @(R a) @(R a) r1 + eval @(R a) @(R a) r2)

instance (FiniteField a, Eq a, ToBits a) => AdditiveMonoid (R a) where
    zero = flip execState mempty $ do
        let con = \z -> (empty, empty, fromList [(z, one)])
        constraint @(R a) @(R a) [con]
        assignment @(R a) @(R a) zero

instance (FiniteField a, Eq a, ToBits a) => AdditiveGroup (R a) where
    negate r = flip execState r $ do
        let x  = toSymbol @a @a $ r1csOutput r
            con = \z -> (empty, empty, fromList [(x, one), (z, one)])
        constraint @(R a) @(R a) [con]
        assignment @(R a) @(R a) (negate . eval @(R a) @(R a) r)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeSemigroup (R a) where
    r1 * r2 = flip execState (r1 <> r2) $ do
        let x1  = toSymbol @a @a $ r1csOutput r1
            x2  = toSymbol @a @a $ r1csOutput r2
            con = \z -> (singleton x1 one, singleton x2 one, singleton z one)
        constraint @(R a) @(R a) [con]
        assignment @(R a) @(R a) (eval @(R a) @(R a) r1 * eval @(R a) @(R a) r2)

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeMonoid (R a) where
    one = mempty { r1csOutput = [0] }

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeGroup (R a) where
    invert r = flip execState r $ do
        let x    = toSymbol @a @a $ r1csOutput r
            con  = \z -> (singleton x one, singleton z one, empty)
        constraint @(R a) @(R a) [con]
        assignment @(R a) @(R a) (bool zero one . (== zero) . eval @(R a) @(R a) r)
        y  <- gets (toSymbol @a @a . r1csOutput)
        -- TODO: remove this constraint
        constraint @(R a) @(R a) [const (singleton y one, singleton y one, singleton y one)]
        let con' = \z -> (singleton x one, singleton z one, fromList [(0, one), (y, negate one)])
        constraint @(R a) @(R a) [con']
        assignment @(R a) @(R a) (invert . eval @(R a) @(R a) r)

instance (FiniteField a, Eq a, ToBits a, FromConstant b a) => FromConstant b (R a) where
    fromConstant c = flip execState mempty $ do
        let x = fromConstant c
            con = \z -> (empty, empty, fromList [(0, x), (z, negate one)])
        constraint @(R a) @(R a) [con]
        assignment @(R a) @(R a) (const x)

------------------------------------- Internal -------------------------------------

-- TODO: Remove the hardcoded constant.
r1csNewVariable :: (Eq a, ToBits a) => (Map Integer a, Map Integer a, Map Integer a) -> Integer
r1csNewVariable (a, b, c) = g a + g b + g c
    where
        z         = toZp 891752917250912079751095709127490 :: Zp BigField
        f (x, y)  = multiExp z (map (toZp :: Integer -> Zp BigField) x) + multiExp z y
        g m       = fromZp $ f $ unzip $ toList m