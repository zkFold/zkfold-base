{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.PlutoEris
 ( PlutoEris_p
 , PlutoEris_q
 , Point_Pluto
 , Point_Eris
 , Point_Triton
 ) where

import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate (toPoly)

-- Designations of curve parameters are as in:
-- https://github.com/daira/pluto-eris

-------------------------- Pluto/Eris curves -------------------------

type PlutoEris_p = 0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5cda8a6c7be4a7a5fe8fadffd6a2a7e8c30006b9459ffffcd300000001
instance Prime PlutoEris_p

type PlutoEris_q = 0x24000000000024000130e0000d7f70e4a803ca76f439266f443f9a5c7a8a6c7be4a775fe8e177fd69ca7e85d60050af41ffffcd300000001
instance Prime PlutoEris_q

instance Field field => WeierstrassCurve "Pluto-Eris" field where
  weierstrassB = fromConstant (57 :: Natural)

type Point_Pluto = Weierstrass "Pluto-Eris" (Point Prelude.Bool (Zp PlutoEris_p))
instance CyclicGroup Point_Pluto where
  type ScalarFieldOf Point_Pluto = Zp PlutoEris_q
  pointGen = pointXY 4 11
instance Scale (Zp PlutoEris_q) Point_Pluto where
  scale n = scale (toConstant n)

type Point_Eris = Weierstrass "Pluto-Eris" (Point Prelude.Bool (Zp PlutoEris_q))
instance CyclicGroup Point_Eris where
  type ScalarFieldOf Point_Eris = Zp PlutoEris_p
  pointGen = pointXY 4 11
instance Scale (Zp PlutoEris_p) Point_Eris where
  scale n = scale (toConstant n)

-------------------------- Triton curve ----------------------------

-- The definition of Triton has not been finalized and is subject to change

instance IrreduciblePoly (Zp PlutoEris_p) "i*sqrt5" where
  irreduciblePoly = toPoly [5, 0, 1]

instance WeierstrassCurve "Triton" (Ext2 (Zp PlutoEris_p) "i*sqrt5") where
  weierstrassB = Ext2 3 1

type Point_Triton =
  Weierstrass "Triton" (Point Prelude.Bool (Ext2 (Zp PlutoEris_p) "i*sqrt5"))
