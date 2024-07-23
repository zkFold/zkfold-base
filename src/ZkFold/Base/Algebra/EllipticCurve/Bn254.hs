{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Bn254 where

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field         (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class

type Bn254_Base = 0x2523648240000001BA344D80000000086121000000000013A700000000000013
instance Prime Bn254_Base

data Bn254

instance EllipticCurve Bn254 where
  type BaseField Bn254 = Zp Bn254_Base
  type ScalarField Bn254 = _

instance StandardEllipticCurve Bn254 where
  aParameter = zero
  bParameter = one + one
