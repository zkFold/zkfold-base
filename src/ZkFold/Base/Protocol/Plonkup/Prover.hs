{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists     #-}

module ZkFold.Base.Protocol.Plonkup.Prover
    ( module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
    , module ZkFold.Base.Protocol.Plonkup.Prover.Secret
    , module ZkFold.Base.Protocol.Plonkup.Prover.Setup
    , plonkupProve
    ) where

import qualified Data.Vector                                         as V
import           Data.Word                                           (Word8)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, pi, sum, take,
                                                                      (!!), (/), (^))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, value)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), PointCompressed, compress)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkupPolyExtendedLength)
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
import           ZkFold.Base.Protocol.Plonkup.Prover.Secret
import           ZkFold.Base.Protocol.Plonkup.Prover.Setup
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

plonkupProve :: forall i n l c1 c2 ts core .
    ( KnownNat n
    , KnownNat (PlonkupPolyExtendedLength n)
    , Ord (BaseField c1)
    , AdditiveGroup (BaseField c1)
    , Arithmetic (ScalarField c1)
    , ToTranscript ts Word8
    , ToTranscript ts (ScalarField c1)
    , ToTranscript ts (PointCompressed c1)
    , FromTranscript ts (ScalarField c1)
    , CoreFunction c1 core
    ) => PlonkupProverSetup i n l c1 c2 -> (PlonkupWitnessInput i c1, PlonkupProverSecret c1) -> (PlonkupInput l c1, PlonkupProof c1)
plonkupProve PlonkupProverSetup {..}
        (PlonkupWitnessInput wInput, PlonkupProverSecret {..})
    = (PlonkupInput wPub, PlonkupProof {..})
    where
        PlonkupCircuitPolynomials {..} = polynomials

        n = value @n
        zhX = polyVecZero @(ScalarField c1) @n @(PlonkupPolyExtendedLength n)

        (w1, w2, w3) = witness relation wInput
        wPub = pubInput relation wInput

        w1X = polyVecInLagrangeBasis omega w1
        w2X = polyVecInLagrangeBasis omega w2
        w3X = polyVecInLagrangeBasis omega w3

        pi  = toPolyVec @(ScalarField c1) @n $ fromList $ fromVector (negate <$> wPub)
        piX = polyVecInLagrangeBasis omega pi

        a = polyVecLinear b1 b2 * zhX + w1X
        b = polyVecLinear b3 b4 * zhX + w2X
        c = polyVecLinear b5 b6 * zhX + w3X

        com = msm @c1 @core
        cmA = gs `com` a
        cmB = gs `com` b
        cmC = gs `com` c

        ts0   = mempty `transcript` compress cmA `transcript` compress cmB `transcript` compress cmC :: ts
        beta  = challenge ts0
        ts1   = ts0 `transcript` (0 :: Word8)
        gamma = challenge ts1

        omegas  = toPolyVec $ V.iterateN (fromIntegral n) (* omega) omega
        omegas' =  V.iterateN (V.length (fromPolyVec z) P.+ 1) (* omega) one
        zs1 = polyVecGrandProduct w1 omegas sigma1s beta gamma
        zs2 = polyVecGrandProduct w2 (scalePV k1 omegas) sigma2s beta gamma
        zs3 = polyVecGrandProduct w3 (scalePV k2 omegas) sigma3s beta gamma
        gp = rewrapPolyVec (V.zipWith (*) (V.zipWith (*) (fromPolyVec zs1) (fromPolyVec zs2))) zs3
        z  = polyVecQuadratic b7 b8 b9 * zhX + polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega gp
        zo = toPolyVec $ V.zipWith (*) (fromPolyVec z) omegas'
        cmZ = gs `com` z

        ts2   = ts1 `transcript` compress cmZ
        alpha = challenge ts2

        t1  = a * b * qmX + a * qlX + b * qrX + c * qoX + piX + qcX
        t2  = (a + polyVecLinear beta gamma)
            * (b + polyVecLinear (beta * k1) gamma)
            * (c + polyVecLinear (beta * k2) gamma)
            * z
        t3  = (a + scalePV beta s1X + scalePV gamma one)
            * (b + scalePV beta s2X + scalePV gamma one)
            * (c + scalePV beta s3X + scalePV gamma one)
            * zo
        t4 = (z - one) * polyVecLagrange @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) 1 omega
        t = (t1 + scalePV alpha (t2 - t3) + scalePV (alpha * alpha) t4) `polyVecDiv` zhX

        t_lo'  = toPolyVec $ V.take (fromIntegral n) $ fromPolyVec t
        t_mid' = toPolyVec $ V.take (fromIntegral n) $ V.drop (fromIntegral n) $ fromPolyVec t
        t_hi'  = toPolyVec $ V.drop (fromIntegral $ 2*n) $ fromPolyVec t
        t_lo   = t_lo' + scalePV b10 (polyVecZero @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) + one)
        t_mid  = t_mid' + scalePV b11 (polyVecZero @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) + one) - scalePV b10 one
        t_hi   = t_hi' - scalePV b11 one
        cmT1   = gs `com` t_lo
        cmT2   = gs `com` t_mid
        cmT3   = gs `com` t_hi

        ts3 = ts2 `transcript` compress cmT1 `transcript` compress cmT2 `transcript` compress cmT3
        xi = challenge ts3

        a_xi  = evalPolyVec a xi
        b_xi  = evalPolyVec b xi
        c_xi  = evalPolyVec c xi
        s1_xi = evalPolyVec s1X xi
        s2_xi = evalPolyVec s2X xi
        z_xi  = evalPolyVec z (xi * omega)
        l1_xi_mul = one // (scale n one * (xi - omega))

        ts4 = ts3 `transcript` a_xi `transcript` b_xi `transcript` c_xi `transcript` s1_xi `transcript` s2_xi `transcript` z_xi
        v   = challenge ts4

        lagrange1_xi = polyVecLagrange @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) 1 omega `evalPolyVec` xi
        zH_xi = zhX `evalPolyVec` xi
        r   = scalePV (a_xi * b_xi) qmX
            + scalePV a_xi qlX
            + scalePV b_xi qrX
            + scalePV c_xi qoX
            + scalePV (piX `evalPolyVec` xi) one
            + qcX
            + scalePV alpha (
                scalePV (
                        (a_xi + beta * xi + gamma)
                    * (b_xi + beta * k1 * xi + gamma)
                    * (c_xi + beta * k2 * xi + gamma)
                    ) z
                - scalePV (
                        (a_xi + beta * s1_xi + gamma)
                    * (b_xi + beta * s2_xi + gamma)
                    * z_xi
                    ) (scalePV beta s3X + scalePV (c_xi + gamma) one)
                )
            + scalePV (alpha * alpha * lagrange1_xi) (z - one)
            - scalePV zH_xi (scalePV (xi^(2 * n)) t_hi + scalePV (xi^n) t_mid + t_lo)

        proof1Poly = (r
                + scalePV v (a - scalePV a_xi one)
                + scalePV (v * v) (b - scalePV b_xi one)
                + scalePV (v * v * v) (c - scalePV c_xi one)
                + scalePV (v * v * v * v) (s1X - scalePV s1_xi one)
                + scalePV (v * v * v * v * v) (s2X - scalePV s2_xi one)
            ) `polyVecDiv` polyVecLinear one (negate xi)

        proof2Poly = (z - scalePV z_xi one) `polyVecDiv` toPolyVec [negate (xi * omega), one]

        proof1 = gs `com` proof1Poly
        proof2 = gs `com` proof2Poly
