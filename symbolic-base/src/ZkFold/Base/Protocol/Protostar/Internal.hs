module ZkFold.Base.Protocol.Protostar.Internal where

import           Numeric.Natural                              (Natural)
import           Prelude                                      (Eq, Integer, Ord, Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate

newtype PolynomialProtostar f c d = PolynomialProtostar (Poly f (Zp c) Natural)
  deriving (Show, Eq, Ord)

deriving instance Polynomial f (Zp c) Natural => AdditiveSemigroup (PolynomialProtostar f c d)

deriving instance Polynomial f (Zp c) Natural => Scale Natural (PolynomialProtostar f c d)

deriving instance Polynomial f (Zp c) Natural => AdditiveMonoid (PolynomialProtostar f c d)

deriving instance Polynomial f (Zp c) Natural => Scale Integer (PolynomialProtostar f c d)

deriving instance Polynomial f (Zp c) Natural => AdditiveGroup (PolynomialProtostar f c d)
