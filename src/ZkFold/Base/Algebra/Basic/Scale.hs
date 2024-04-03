{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Algebra.Basic.Scale where

import           Prelude                         hiding (sum, (*), (+))

import           ZkFold.Base.Algebra.Basic.Class

newtype BinScale b a = BinScale { runBinScale :: a }
    deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, MultiplicativeSemigroup, MultiplicativeMonoid)

deriving newtype instance FromConstant c a => FromConstant c (BinScale b a)

deriving newtype instance Semiring a => Semiring (BinScale b a)

deriving newtype instance Ring a => Ring (BinScale b a)

instance (AdditiveMonoid a, Eq b, BinaryExpansion b) => Scale (BinScale b a) b where
    scale n a = sum $ zipWith f (binaryExpansion n) (iterate (\x -> x + x) a)
      where
        f x y
          | x == zero = zero
          | x == one  = y
          | otherwise = error "scale: This should never happen."
