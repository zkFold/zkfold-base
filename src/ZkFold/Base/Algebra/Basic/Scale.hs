{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Algebra.Basic.Scale where

import ZkFold.Base.Algebra.Basic.Class
import Prelude hiding (sum, (*), (+))

newtype BinScale b a = BinScale {runBinScale :: a}
  deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, MultiplicativeSemigroup, MultiplicativeMonoid)

deriving newtype instance (FromConstant c a) => FromConstant c (BinScale b a)

deriving newtype instance (Semiring a) => Semiring (BinScale b a)

deriving newtype instance (Ring a) => Ring (BinScale b a)

instance (AdditiveMonoid a, Eq b, BinaryExpansion b) => Scale (BinScale b a) b where
  scale n a = sum $ zipWith f (binaryExpansion n) (iterate (\x -> x + x) a)
    where
      f x y
        | x == zero = zero
        | x == one = y
        | otherwise = error "scale: This should never happen."

newtype Self a = Self {getSelf :: a}
  deriving (Eq)
  deriving newtype
    ( AdditiveSemigroup,
      AdditiveMonoid,
      AdditiveGroup,
      MultiplicativeSemigroup,
      MultiplicativeMonoid,
      MultiplicativeGroup,
      BinaryExpansion
    )

deriving newtype instance (FromConstant c a) => FromConstant c (Self a)

deriving newtype instance (Semiring a) => Semiring (Self a)

deriving newtype instance (Ring a) => Ring (Self a)

deriving newtype instance (Field a) => Field (Self a)

deriving newtype instance (Finite a) => Finite (Self a)

instance (Ring a) => Scale (Self a) a where
  scale a (Self b) = Self (a * b)

scale' :: (Ring a) => a -> a -> a
scale' a b = getSelf $ scale a (Self b)
