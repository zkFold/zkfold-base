{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Algebra.Basic.Scale where

import           Prelude                         hiding (sum, (*), (+))

import           ZkFold.Base.Algebra.Basic.Class

newtype BinScale b a = BinScale { runBinScale :: a }
    deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, MultiplicativeSemigroup, MultiplicativeMonoid)

instance (AdditiveMonoid a, Eq b, BinaryExpansion b) => Scale (BinScale b a) b where
    scale n a = sum $ zipWith f (binaryExpansion n) (iterate (\x -> x + x) a)
      where
        f x y
          | x == zero = zero
          | x == one  = y
          | otherwise = error "scale: This should never happen."

newtype Self a = Self { getSelf :: a }
    deriving (Eq)
    deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup,
                      MultiplicativeSemigroup, MultiplicativeMonoid, MultiplicativeGroup,
                      BinaryExpansion, Finite)

instance Ring a => Scale (Self a) a where
    scale a (Self b) = Self (a * b)

scale' :: Ring a => a -> a -> a
scale' a b = getSelf $ scale a (Self b)