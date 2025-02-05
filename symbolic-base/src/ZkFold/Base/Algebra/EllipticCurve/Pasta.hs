{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Pasta
  ( Pasta_Point
  , Pallas_Point
  , Vesta_Point
  , FpModulus
  , FqModulus
  , Fp
  , Fq
  ) where

import           Control.Monad
import           Prelude                                 (type (~), ($))
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.ByteString
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq

-------------------------------- Introducing Fields ----------------------------------

type FpModulus = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
instance Prime FpModulus

type FqModulus = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
instance Prime FqModulus

type Fp = Zp FpModulus
type Fq = Zp FqModulus

------------------------------------ Pasta -------------------------------------

instance Field field => WeierstrassCurve "Pasta" field where
  weierstrassB = fromConstant (5 :: Natural)

type Pasta_Point field = Weierstrass "Pasta" (Point field)

------------------------------------ Pallas ------------------------------------

type Pallas_Point = Pasta_Point Fp

instance CyclicGroup Pallas_Point where
  type ScalarFieldOf Pallas_Point = Fq
  pointGen = pointXY
    0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000
    0x02

instance Scale Fq Pallas_Point where
    scale n x = scale (toConstant n) x

------------------------------------ Vesta ------------------------------------

type Vesta_Point = Pasta_Point Fq

instance CyclicGroup Vesta_Point where
  type ScalarFieldOf Vesta_Point = Fp
  pointGen = pointXY
    0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000
    0x02

instance Scale Fp Vesta_Point where
    scale n x = scale (toConstant n) x

------------------------------------ Encoding ------------------------------------

instance
  ( Binary field
  , Field field
  , Eq field
  , BooleanOf field ~ Prelude.Bool
  ) => Binary (Pasta_Point field) where
    put (Weierstrass (Point xp yp isInf)) =
      if isInf
      then put @(Pasta_Point field) (pointXY zero zero)
      else put xp >> put yp
    get = do
      xp <- get
      yp <- get
      return $
        if xp == zero && yp == zero
        then pointInf
        else pointXY xp yp
