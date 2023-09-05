{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Arithmetization.R1CS (
        R1CS,
        r1csSize,
        r1csWitnessLength,
        r1csOptimize,
        r1csCompile        
    ) where

import           Data.List                   (nub)
import           Data.Map                    hiding (map)
import           Prelude                     hiding (Num(..), length, length)

import           ZkFold.Crypto.Algebra.Class
import           ZkFold.Prelude (length)

-- | A rank-1 constraint system.
data R1CS a = R1CS
    {
        r1csMatrices :: Map Integer (Map Integer a, Map Integer a, Map Integer a),
        r1csWitness  :: Map Integer a -> Map Integer a,
        r1csOutput   :: Integer
    }

r1csSize :: R1CS a -> Integer
r1csSize = length . r1csMatrices

r1csWitnessLength :: R1CS a -> Integer
r1csWitnessLength r =
    let m = elems (r1csMatrices r)
        f (a, b, c) = maximum $ keys a ++ keys b ++ keys c
    in maximum (map f m) + 1

-- TODO: Implement this.
r1csOptimize :: R1CS a -> R1CS a
r1csOptimize = undefined

r1csCompile :: forall c b . (FiniteField c, Eq c) => (forall a. FiniteField a => a -> b) -> b
r1csCompile f = f (zero :: R1CS c)

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

r1csAddConstraint :: R1CS a -> (Map Integer a, Map Integer a, Map Integer a) -> R1CS a
r1csAddConstraint r (a, b, c) = r
    {
        r1csMatrices = insert (r1csSize r) (a, b, c) (r1csMatrices r)
    }

instance (FiniteField a, Eq a) => AdditiveSemigroup (R1CS a) where
    r1 + r2 =
        let r  = r1csMerge r1 r2
            x1 = r1csOutput r1
            x2 = r1csOutput r2
            x  = r1csWitnessLength r
            r' = r1csAddConstraint r
                (empty, empty, fromList [(x1, one), (x2, one), (x, negate one)])
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                    y2 = a ! x2
                in insert x (y1 + y2) a,
            r1csOutput = x
        }

instance (FiniteField a, Eq a) => AdditiveMonoid (R1CS a) where
    zero = R1CS empty (const (singleton 0 one)) 0

instance (FiniteField a, Eq a) => AdditiveGroup (R1CS a) where
    negate r =
        let x1 = r1csOutput r
            x  = r1csWitnessLength r
            r' = r1csAddConstraint r
                (empty, empty, fromList [(x1, one), (x, one)])
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                in insert x (negate y1) a,
            r1csOutput = x
        }

instance (FiniteField a, Eq a) => MultiplicativeSemigroup (R1CS a) where
    r1 * r2 =
        let r  = r1csMerge r1 r2
            x1 = r1csOutput r1
            x2 = r1csOutput r2
            x  = r1csWitnessLength r
            r' = r1csAddConstraint r
                (singleton x1 one, singleton x2 one, singleton x one)
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                    y2 = a ! x2
                in insert x (y1 * y2) a,
            r1csOutput = x
        }

instance (FiniteField a, Eq a) => MultiplicativeMonoid (R1CS a) where
    one = R1CS empty (const (singleton 0 one)) 0

instance (FiniteField a, Eq a) => MultiplicativeGroup (R1CS a) where
    invert r =
        let x1 = r1csOutput r
            x  = r1csWitnessLength r
            r' = r1csAddConstraint r
                (singleton x1 one, singleton x one, singleton 0 one)
        in r'
        {
            r1csWitness = \w ->
                let a = r1csWitness r w
                    y1 = a ! x1
                in insert x (invert y1) a,
            r1csOutput = x
        }

instance (FiniteField a, Eq a) => FiniteField (R1CS a) where
    order  _ = order (zero :: a)