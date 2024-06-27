module ZkFold.Base.Protocol.ARK.Protostar.Internal where

import           Numeric.Natural                              (Natural)
import           Prelude                                      (Eq, Show, Ord, Integer)

import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Base.Algebra.Basic.Class              (AdditiveSemigroup, AdditiveMonoid, Scale, AdditiveGroup)

newtype PolynomialProtostar c n d = PolynomialProtostar (Poly c (Zp n) Natural)
  deriving (Show, Eq, Ord)
  
deriving instance Polynomial c (Zp n) Natural => AdditiveSemigroup (PolynomialProtostar c n d)

deriving instance Polynomial c (Zp n) Natural => Scale Natural (PolynomialProtostar c n d)

deriving instance Polynomial c (Zp n) Natural => AdditiveMonoid (PolynomialProtostar c n d)

deriving instance Polynomial c (Zp n) Natural => Scale Integer (PolynomialProtostar c n d)

deriving instance Polynomial c (Zp n) Natural => AdditiveGroup (PolynomialProtostar c n d)