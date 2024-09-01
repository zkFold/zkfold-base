{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier
    ( module ZkFold.Base.Protocol.Plonkup.Verifier.Commitments
    , module ZkFold.Base.Protocol.Plonkup.Verifier.Setup
    , plonkupVerify
    ) where

import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, value)
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof            hiding (verify)
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments
import           ZkFold.Base.Protocol.Plonkup.Verifier.Setup
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

plonkupVerify :: forall i n l c1 c2 ts .
    ( KnownNat n
    , KnownNat (PlonkupPolyExtendedLength n)
    , Pairing c1 c2
    , Ord (BaseField c1)
    , AdditiveGroup (BaseField c1)
    , Arithmetic (ScalarField c1)
    , ToTranscript ts (ScalarField c1)
    , ToTranscript ts (PointCompressed c1)
    , FromTranscript ts (ScalarField c1)
    ) => PlonkupVerifierSetup i n l c1 c2 -> PlonkupInput l c1 -> PlonkupProof c1 -> Bool
plonkupVerify
    PlonkupVerifierSetup {..}
    (PlonkupInput wPub)
    (PlonkupProof cmA cmB cmC cmZ cmT1 cmT2 cmT3 proof1 proof2 a_xi b_xi c_xi s1_xi s2_xi z_xi _) = p1 == p2
    where
        PlonkupCircuitCommitments {..} = commitments

        n = value @n

        (beta, ts) = challenge $ mempty
            `transcript` compress cmA
            `transcript` compress cmB
            `transcript` compress cmC :: (ScalarField c1, ts)
        (gamma, ts') = challenge ts

        (alpha, ts'') = challenge $ ts' `transcript` compress cmZ

        (xi, ts''') = challenge $ ts''
            `transcript` compress cmT1
            `transcript` compress cmT2
            `transcript` compress cmT3

        (v, ts'''') = challenge $ ts'''
            `transcript` a_xi
            `transcript` b_xi
            `transcript` c_xi
            `transcript` s1_xi
            `transcript` s2_xi
            `transcript` z_xi

        (u, _) = challenge $ ts''''
            `transcript` compress proof1
            `transcript` compress proof2

        zH_xi        = polyVecZero @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) `evalPolyVec` xi
        lagrange1_xi = polyVecLagrange @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) 1 omega `evalPolyVec` xi
        pubPoly_xi   = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega (toPolyVec $ fromList $ fromVector (negate <$> wPub)) `evalPolyVec` xi

        r0 =
                pubPoly_xi
            - alpha * alpha * lagrange1_xi
            - alpha
                * (a_xi + beta * s1_xi + gamma)
                * (b_xi + beta * s2_xi + gamma)
                * (c_xi + gamma)
                * z_xi
        d  =
                mul (a_xi * b_xi) cmQm
            + mul a_xi cmQl
            + mul b_xi cmQr
            + mul c_xi cmQo
            + cmQc
            + mul (
                        alpha
                    * (a_xi + beta * xi + gamma)
                    * (b_xi + beta * k1 * xi + gamma)
                    * (c_xi + beta * k2 * xi + gamma)
                +     alpha * alpha * lagrange1_xi
                +     u
                ) cmZ
            - mul (
                    alpha
                * beta
                * (a_xi + beta * s1_xi + gamma)
                * (b_xi + beta * s2_xi + gamma)
                * z_xi
                ) cmS3
            - mul zH_xi (cmT1 + (xi^n) `mul` cmT2 + (xi^(2*n)) `mul` cmT3)
        f  =
                d
            + v `mul` cmA
            + (v * v) `mul` cmB
            + (v * v * v) `mul` cmC
            + (v * v * v * v) `mul` cmS1
            + (v * v * v * v * v) `mul` cmS2
        e  = (
            negate r0
            + v * a_xi
            + v * v * b_xi
            + v * v * v * c_xi
            + v * v * v * v * s1_xi
            + v * v * v * v * v * s2_xi
            + u * z_xi
            ) `mul` gen

        p1 = pairing @c1 @c2 (xi `mul` proof1 + (u * xi * omega) `mul` proof2 + f - e) (gen :: Point c2)
        p2 = pairing (proof1 + u `mul` proof2) h1
