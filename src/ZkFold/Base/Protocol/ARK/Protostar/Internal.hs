module ZkFold.Base.Protocol.ARK.Protostar.Internal where

import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (MonomialBoundedDegree, PolynomialBoundedDegree)

type MonomialPorotostar n d = MonomialBoundedDegree (Zp n) d

type PolynomialProtostar c n d = PolynomialBoundedDegree c (Zp n) d
