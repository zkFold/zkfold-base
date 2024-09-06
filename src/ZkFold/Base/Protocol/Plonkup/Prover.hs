{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.Plonkup.Prover
    ( module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
    , module ZkFold.Base.Protocol.Plonkup.Prover.Secret
    , module ZkFold.Base.Protocol.Plonkup.Prover.Setup
    , plonkupProve
    ) where

import           Data.Bool                                           (bool)
import qualified Data.Vector                                         as V
import           Data.Word                                           (Word8)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, pi, sum, take,
                                                                      (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, Natural, value)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), PointCompressed, compress)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkupPolyExtended, PlonkupPolyExtendedLength)
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
import           ZkFold.Base.Protocol.Plonkup.Prover.Secret
import           ZkFold.Base.Protocol.Plonkup.Prover.Setup
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Testing                (PlonkupProverTestInfo(..))
import           ZkFold.Base.Protocol.Plonkup.Utils                  (sortByList)
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
    ) => PlonkupProverSetup i n l c1 c2 -> (PlonkupWitnessInput i c1, PlonkupProverSecret c1) -> (PlonkupInput l c1, PlonkupProof c1, PlonkupProverTestInfo n c1)
plonkupProve PlonkupProverSetup {..}
        (PlonkupWitnessInput wInput, PlonkupProverSecret {..})
    = (PlonkupInput wPub, PlonkupProof {..}, PlonkupProverTestInfo {..})
    where
        PlonkupCircuitPolynomials {..} = polynomials

        n = value @n
        zhX = polyVecZero @_ @n @(PlonkupPolyExtendedLength n)

        (w1, w2, w3) = witness relation wInput
        wPub = pubInput relation wInput

        w1X = polyVecInLagrangeBasis omega w1 :: PlonkupPolyExtended n c1
        w2X = polyVecInLagrangeBasis omega w2 :: PlonkupPolyExtended n c1
        w3X = polyVecInLagrangeBasis omega w3 :: PlonkupPolyExtended n c1

        pi  = toPolyVec @_ @n $ fromList $ fromVector (negate <$> wPub)
        piX = polyVecInLagrangeBasis omega pi  :: PlonkupPolyExtended n c1

        -- Round 1

        aX = polyVecLinear b1 b2 * zhX + w1X :: PlonkupPolyExtended n c1
        bX = polyVecLinear b3 b4 * zhX + w2X :: PlonkupPolyExtended n c1
        cX = polyVecLinear b5 b6 * zhX + w3X :: PlonkupPolyExtended n c1

        com = msm @c1 @core @_ @(PlonkupPolyExtendedLength n)
        cmA = gs `com` aX
        cmB = gs `com` bX
        cmC = gs `com` cX

        -- Round 2

        ts1   = mempty
            `transcript` compress cmA
            `transcript` compress cmB
            `transcript` compress cmC :: ts
        -- zeta = challenge ts1 :: ScalarField c1

        t_zeta = t relation
        f_zeta = fromList $ zipWith3 (\lk ti ai -> bool ti ai (lk == one)) (toList $ qK relation) (toList $ t relation) (toList w1) :: PolyVec (ScalarField c1) n

        fX = polyVecLinear b7 b8 * zhX + polyVecInLagrangeBasis omega f_zeta :: PlonkupPolyExtended n c1

        s  = sortByList (toList f_zeta ++ toList t_zeta) (toList t_zeta)
        h1 = toPolyVec $ V.ifilter (\i _ -> odd i) $ fromList s  :: PolyVec (ScalarField c1) n
        h2 = toPolyVec $ V.ifilter (\i _ -> even i) $ fromList s :: PolyVec (ScalarField c1) n

        h1X = polyVecQuadratic b9 b10 b11 * zhX + polyVecInLagrangeBasis omega h1 :: PlonkupPolyExtended n c1
        h2X = polyVecLinear b12 b13 * zhX + polyVecInLagrangeBasis omega h2 :: PlonkupPolyExtended n c1

        cmF  = gs `com` fX
        cmH1 = gs `com` h1X
        cmH2 = gs `com` h2X

        -- Round 3

        ts2 = ts1
            `transcript` compress cmF
            `transcript` compress cmH1
            `transcript` compress cmH2
        beta    = challenge (ts2 `transcript` (1 :: Word8))
        gamma   = challenge (ts2 `transcript` (2 :: Word8))
        delta   = challenge (ts2 `transcript` (3 :: Word8))
        epsilon = challenge (ts2 `transcript` (4 :: Word8))

        omegas  = toPolyVec $ V.iterateN (fromIntegral n) (* omega) one
        omegas' = toPolyVec $ V.iterateN (fromIntegral $ value @(PlonkupPolyExtendedLength n)) (* omega) one

        cumprod :: PolyVec (ScalarField c1) n -> PolyVec (ScalarField c1) n
        cumprod = toPolyVec . V.scanl' (*) one . fromPolyVec

        rot1 :: PolyVec (ScalarField c1) n -> PolyVec (ScalarField c1) n
        rot1 p = toPolyVec $ V.drop 1 (fromPolyVec p) V.++ V.take 1 (fromPolyVec p)

        -- TODO: check operation order
        grandProduct1 = cumprod $
                (w1 + beta *. omegas .+ gamma)
            .*. (w2 + (beta * k1) *. omegas .+ gamma)
            .*. (w3 + (beta * k2) *. omegas .+ gamma)
            ./. (w1 + beta *. sigma1s .+ gamma)
            ./. (w2 + beta *. sigma2s .+ gamma)
            ./. (w3 + beta *. sigma3s .+ gamma)
        z1 = polyVecQuadratic b14 b15 b16 * zhX + polyVecInLagrangeBasis omega grandProduct1 :: PlonkupPolyExtended n c1

        grandProduct2 = cumprod $
                (one + delta) *. (epsilon +. f_zeta)
            .*. ((epsilon * (one + delta)) +. t_zeta + delta *. rot1 t_zeta)
            ./. ((epsilon * (one + delta)) +. h1 + delta *. h2)
            ./. ((epsilon * (one + delta)) +. h2 + delta *. rot1 h1)
        z2 = polyVecQuadratic b17 b18 b19 * zhX + polyVecInLagrangeBasis omega grandProduct2 :: PlonkupPolyExtended n c1

        cmZ1 = gs `com` z1
        cmZ2 = gs `com` z2

        -- Round 4

        ts3 = ts2
            `transcript` compress cmZ1
            `transcript` compress cmZ2
        alpha  = challenge ts3
        alpha2 = alpha * alpha
        alpha3 = alpha2 * alpha
        alpha4 = alpha3 * alpha
        alpha5 = alpha4 * alpha

        qX = (
                (qmX * aX * bX + qlX * aX + qrX * bX + qoX * cX + piX + qcX)
              + (polyVecLinear beta gamma + aX) * (polyVecLinear (beta * k1) gamma + bX) * (polyVecLinear (beta * k2) gamma + cX) * z1 .* alpha
              - (aX + beta *. s1X .+ gamma) * (bX + beta *. s2X .+ gamma) * (cX + beta *. s3X .+ gamma) * (z1 .*. omegas') .* alpha
              + (z1 - one) * polyVecLagrange @_ @n 1 omega .* alpha2
              + qkX * (aX - fX) .* alpha3
              + z2 .* (one + delta) .*. (epsilon +. fX) .*. ((epsilon * (one + delta)) +. tX + delta *. (tX .*. omegas')) .* alpha4
              - (z2 .*. omegas') * ((epsilon * (one - delta)) +. h1X + delta *. h2X) * ((epsilon * (one - delta)) +. h2X + delta *. (h1X .*. omegas')) .* alpha4
              + (z2 - one) * polyVecLagrange @_ @n 1 omega .* alpha5
            ) `polyVecDiv` zhX
        qlowX  = toPolyVec $ V.take (fromIntegral (n+2)) $ fromPolyVec qX
        qmidX  = toPolyVec $ V.take (fromIntegral (n+2)) $ V.drop (fromIntegral (n+2)) $ fromPolyVec qX
        qhighX = toPolyVec $ V.drop (fromIntegral (2*(n+2))) $ fromPolyVec qX

        cmQlow = gs `com` qlowX
        cmQmid = gs `com` qmidX
        cmQhigh = gs `com` qhighX

        -- Round 5

        ts4 = ts3
            `transcript` compress cmQlow
            `transcript` compress cmQmid
            `transcript` compress cmQhigh
        xi = challenge ts4

        a_xi  = aX `evalPolyVec` xi
        b_xi  = bX `evalPolyVec` xi
        c_xi  = cX `evalPolyVec` xi
        s1_xi = s1X `evalPolyVec` xi
        s2_xi = s2X `evalPolyVec` xi
        f_xi  = fX `evalPolyVec` xi
        t_xi  = tX `evalPolyVec` xi
        t_xi' = tX `evalPolyVec` (xi * omega)
        z1_xi = z1 `evalPolyVec` (xi * omega)
        z2_xi = z2 `evalPolyVec` (xi * omega)
        h1_xi = h1X `evalPolyVec` (xi * omega)
        h2_xi = h2X `evalPolyVec` xi
        lag1_xi = polyVecLagrange @_ @n @(PlonkupPolyExtendedLength n) 1 omega `evalPolyVec` xi

        -- Round 6

        ts5 = ts4
            `transcript` a_xi
            `transcript` b_xi
            `transcript` c_xi
            `transcript` s1_xi
            `transcript` s2_xi
            `transcript` f_xi
            `transcript` t_xi
            `transcript` t_xi'
            `transcript` z1_xi
            `transcript` z2_xi
            `transcript` h1_xi
            `transcript` h2_xi
        v = challenge ts5

        pi_xi = piX `evalPolyVec` xi
        zhX_xi = zhX `evalPolyVec` xi

        rX =
                qmX .* (a_xi * b_xi) + qlX .* a_xi + qrX .* b_xi + qoX .* c_xi .+ pi_xi + qcX
              + alpha *. (((a_xi + beta * xi + gamma) * (b_xi + beta * k1 * xi + gamma) * (c_xi + beta * k2 * xi + gamma)) *. z1
                        - ((a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * z1_xi) *. (c_xi +. s3X .+ gamma)
                    )
              + (alpha2 * lag1_xi) *. (z1 - one)
              + (alpha3 * (a_xi - f_xi)) *. qkX
              + alpha4 *. (((one + delta) * (epsilon + f_xi) * ((epsilon * (one + delta)) + t_xi + delta * t_xi')) *. z2
                        - (z2_xi * ((epsilon * (one + delta)) + h2_xi + delta * h1_xi)) *. ((epsilon * (one + delta)) +. h1X .+ (delta * h2_xi))
                    )
              + (alpha5 * lag1_xi) *. (z2 - one)
              - zhX_xi *. (qlowX + (xi^(n+2) *. qmidX) + (xi^(2*n+4)) *. qhighX)

        vn i = v ^ (i :: Natural)

        proofX1 = (
                  rX
                + (vn 1 *. (aX - (a_xi *. one)))
                + (vn 2 *. (bX - (b_xi *. one)))
                + (vn 3 *. (cX - (c_xi *. one)))
                + (vn 4 *. (s1X - (s1_xi *. one)))
                + (vn 5 *. (s2X - (s2_xi *. one)))
                + (vn 6 *. (fX - (f_xi *. one)))
                + (vn 7 *. (h2X - (h2_xi *. one)))
                + (vn 8 *. (tX - (t_xi *. one)))
            ) `polyVecDiv` polyVecLinear one (negate xi)
        proofX2 = (
                  z1 - (z1_xi *. one)
                + (vn 1 *. (tX - (t_xi' *. one)))
                + (vn 2 *. (z2 - (z2_xi *. one)))
                + (vn 3 *. (h1X - (h1_xi *. one)))
            ) `polyVecDiv` polyVecLinear one (negate (xi * omega))

        proof1 = gs `com` proofX1
        proof2 = gs `com` proofX2
