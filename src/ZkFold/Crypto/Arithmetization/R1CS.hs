{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Arithmetization.R1CS (
        Arithmetizable(..),
        BigField,
        R1CS,
        r1csSizeN,
        r1csSizeM,
        r1csX,
        r1csCompile,
        r1csOptimize,
        r1csPrint
    ) where

import           Data.List                   (nub)
import           Data.Map                    hiding (map, foldr)
import           Prelude                     hiding (Num(..), (+), (^), product, length)
import           Text.Pretty.Simple          (pPrint)

import           ZkFold.Crypto.Algebra.Class
import           ZkFold.Crypto.Algebra.Field
import           ZkFold.Prelude              (length)

-- TODO: Move this elsewhere.
class Arithmetizable a b where
    arithmetize :: b -> a

instance Arithmetizable a a where
    arithmetize = id

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
-- TODO: support functions that output objects representable by multiple R1CS variables.
data R1CS a = R1CS
    {
        r1csMatrices :: Map Integer (Map Integer a, Map Integer a, Map Integer a),
        -- ^ The R1CS matrices
        r1csWitness  :: Map Integer a -> Map Integer a,
        -- ^ The witness generation function
        r1csOutput   :: Integer
        -- ^ The current variable index
    }

-- | Calculates the number of constraints in the system.
r1csSizeN :: R1CS a -> Integer
r1csSizeN = length . r1csMatrices

-- | Calculates the number of variables in the system.
r1csSizeM :: R1CS a -> Integer
r1csSizeM r = length $ nub $ concatMap (keys . f) (elems $ r1csMatrices r)
    where f (a, b, c) = a `union` b `union` c

-- | The input variable.
r1csX :: FiniteField a => R1CS a
r1csX = R1CS empty (insert 0 one) 1

-- | Compiles a function into a R1CS.
r1csCompile :: forall c . (FiniteField c, Eq c, ToBits c) =>
    (forall a . (FiniteField a) => a -> a) -> R1CS c
r1csCompile f = f (r1csX :: R1CS c)

-- | Optimizes the constraint system.
--
-- TODO: Implement this
r1csOptimize :: R1CS a -> R1CS a
r1csOptimize = undefined

-- | Prints the constraint system, the witness, and the output on a given input.
--
-- TODO: Move this elsewhere
r1csPrint :: (Show a) => R1CS a -> a -> IO ()
r1csPrint r x = do
    let m = elems (r1csMatrices r)
        w = r1csWitness r (singleton 1 x)
        o = r1csOutput r
    putStr "Matrices: "
    pPrint m
    putStr "Witness: "
    pPrint w
    putStr "Output: "
    pPrint o
    putStr"Value: "
    pPrint $ w ! o

------------------------------------- Instances -------------------------------------

{-| To compile a function @f :: C a => a -> a@, we must define an instance @C (R1CS a)@.
    Keep in mind that the more type constraints we impose on the polymorphic argument @a@,
    the broader the class of functions that can be compiled.
|-}

instance (FiniteField a, Eq a, ToBits a) => AdditiveSemigroup (R1CS a) where
    r1 + r2 =
        let r   = r1csMerge r1 r2
            x1  = r1csOutput r1
            x2  = r1csOutput r2
            con = \z -> (empty, empty, fromListWith (+) [(x1, one), (x2, one), (z, negate one)])
            r'  = r1csAddConstraint r con
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                    y2 = a ! x2
                in insert (r1csOutput r') (y1 + y2) a
        }

instance (FiniteField a, Eq a, ToBits a) => AdditiveMonoid (R1CS a) where
    zero =
        let r = R1CS empty (insert 0 one) 0
            con = \z -> (empty, empty, fromList [(z, one)])
            r' = r1csAddConstraint r con
        in r'
        {
            r1csWitness = insert (r1csOutput r') zero . r1csWitness r
        }

instance (FiniteField a, Eq a, ToBits a) => AdditiveGroup (R1CS a) where
    negate r =
        let x1 = r1csOutput r
            con = \z -> (empty, empty, fromList [(x1, one), (z, one)])
            r' = r1csAddConstraint r con
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                in insert (r1csOutput r') (negate y1) a
        }

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeSemigroup (R1CS a) where
    r1 * r2 =
        let r  = r1csMerge r1 r2
            x1 = r1csOutput r1
            x2 = r1csOutput r2
            con = \z -> (singleton x1 one, singleton x2 one, singleton z one)
            r' = r1csAddConstraint r con
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                    y2 = a ! x2
                in insert (r1csOutput r') (y1 * y2) a
        }

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeMonoid (R1CS a) where
    one = R1CS empty (insert 0 one) 0

instance (FiniteField a, Eq a, ToBits a) => MultiplicativeGroup (R1CS a) where
    invert r =
        let x1 = r1csOutput r
            con = \z -> (singleton x1 one, singleton z one, singleton 0 one)
            r' = r1csAddConstraint r con
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                in insert (r1csOutput r') (invert y1) a
        }

instance (FiniteField a) => Finite (R1CS a) where
    order = order @a

------------------------------------- Internal -------------------------------------

r1csMerge :: Eq a => R1CS a -> R1CS a -> R1CS a
r1csMerge r1 r2 = R1CS
    {
        r1csMatrices =
            let m1 = elems $ r1csMatrices r1
                m2 = elems $ r1csMatrices r2
            in fromList $ zip [0..] $ nub (m1 ++ m2),
        r1csWitness = \w -> r1csWitness r1 w `union` r1csWitness r2 w,
        r1csOutput  = 0
    }

-- TODO: Remove the hardcoded constant.
r1csNewVariable :: (Eq a, ToBits a) => (Map Integer a, Map Integer a, Map Integer a) -> Integer
r1csNewVariable (a, b, c) = g a + g b + g c
    where
        z         = toZp 891752917250912079751095709127490 :: Zp BigField
        f (x, y)  = multiExp z (map (toZp :: Integer -> Zp BigField) x) + multiExp z y
        g m       = fromZp $ f $ unzip $ toList m

r1csAddConstraint :: (Eq a, ToBits a) => R1CS a -> (Integer -> (Map Integer a, Map Integer a, Map Integer a)) -> R1CS a
r1csAddConstraint r con =
    let x = r1csNewVariable (con $ -1)
    in r
    {
        r1csMatrices = insert (r1csSizeN r) (con x) (r1csMatrices r),
        r1csOutput   = x
    }