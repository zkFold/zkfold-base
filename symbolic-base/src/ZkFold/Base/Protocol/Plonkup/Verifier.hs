{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier
    ( module ZkFold.Base.Protocol.Plonkup.Verifier.Commitments
    , module ZkFold.Base.Protocol.Plonkup.Verifier.Setup
    , plonkupVerify
    ) where

import           Data.Word                                           (Word8)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), Ord (..), drop, length, sum,
                                                                      take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, Natural, value)
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Protocol.NonInteractiveProof            hiding (verify)
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments
import           ZkFold.Base.Protocol.Plonkup.Verifier.Setup

plonkupVerify :: forall p i n l scalarField g1 g2 gt c1 c2 f1 f2 pt1 pt2 cp1 ts.
    ( KnownNat n
    , KnownNat (PlonkupPolyExtendedLength n)
    , Foldable l
    , SubgroupCurve c1 Bool f1 scalarField pt1
    , SubgroupCurve c2 Bool f2 scalarField pt2
    , SymmetricCurve c1 Bool f1 pt1 cp1
    , g1 ~ pt1 f1
    , g2 ~ pt2 f2
    , Pairing scalarField g1 g2 gt
    , Eq scalarField
    , Eq gt
    , ToTranscript ts Word8
    , ToTranscript ts scalarField
    , ToTranscript ts (cp1 f1)
    , FromTranscript ts scalarField
    ) => PlonkupVerifierSetup p i n l scalarField g1 g2 -> PlonkupInput l scalarField -> PlonkupProof g1 scalarField -> Bool
plonkupVerify
    PlonkupVerifierSetup {..}
    (PlonkupInput wPub)
    (PlonkupProof {..}) = p1 == p2
    where
        PlonkupCircuitCommitments {..} = commitments

        n = value @n

        -- Step 4: Compute challenges

        compress = compressPoint @c1 @Bool

        ts1   = mempty
            `transcript` compress cmA
            `transcript` compress cmB
            `transcript` compress cmC :: ts

        ts2 = ts1
            `transcript` compress cmF
            `transcript` compress cmH1
            `transcript` compress cmH2
        beta    = challenge (ts2 `transcript` (1 :: Word8))
        gamma   = challenge (ts2 `transcript` (2 :: Word8))
        delta   = challenge (ts2 `transcript` (3 :: Word8))
        epsilon = challenge (ts2 `transcript` (4 :: Word8))

        ts3 = ts2
            `transcript` compress cmZ1
            `transcript` compress cmZ2
        alpha  = challenge ts3
        alpha2 = alpha * alpha
        alpha3 = alpha2 * alpha
        alpha4 = alpha3 * alpha
        alpha5 = alpha4 * alpha

        ts4 = ts3
            `transcript` compress cmQlow
            `transcript` compress cmQmid
            `transcript` compress cmQhigh
        xi = challenge ts4

        ts5 = ts4
            `transcript` a_xi
            `transcript` b_xi
            `transcript` c_xi
            `transcript` s1_xi
            `transcript` s2_xi
            `transcript` f_xi
            `transcript` t_xi
            `transcript` t_xi'
            `transcript` z1_xi'
            `transcript` z2_xi'
            `transcript` h1_xi'
            `transcript` h2_xi
        v = challenge ts5
        vn i = v ^ (i :: Natural)

        ts6 = ts5
            `transcript` compress proof1
            `transcript` compress proof2
        eta = challenge ts6

        -- Step 5: Compute zero polynomial evaluation
        zhX_xi = polyVecZero @scalarField @n @(PlonkupPolyExtendedLength n) `evalPolyVec` xi :: scalarField

        -- Step 6: Compute Lagrange polynomial evaluation
        lagrange1_xi = polyVecLagrange @scalarField @n @(PlonkupPolyExtendedLength n) 1 omega `evalPolyVec` xi

        -- Step 7: Compute public polynomial evaluation
        pi_xi = polyVecInLagrangeBasis @scalarField @n @(PlonkupPolyExtendedLength n) omega
            (toPolyVec $ fromList $ foldMap (\x -> [negate x]) wPub)
            `evalPolyVec` xi

        -- Step 8: Compute the public table commitment
        cmT_zeta = cmT1

        -- Step 9: Compute r0
        r0 = pi_xi
            - alpha * (a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * (c_xi + gamma) * z1_xi'
            - alpha2 * lagrange1_xi
            - alpha4 * z2_xi' * (epsilon * (one + delta) + delta * h2_xi) * (epsilon * (one + delta) + h2_xi + delta * h1_xi')
            - alpha5 * lagrange1_xi

        -- Step 10: Compute D
        d =     (a_xi * b_xi) `scale` cmQm + a_xi `scale` cmQl + b_xi `scale` cmQr + c_xi `scale` cmQo + cmQc
              + ((a_xi + beta * xi + gamma) * (b_xi + beta * k1 * xi + gamma) * (c_xi + beta * k2 * xi + gamma) * alpha + lagrange1_xi * alpha2) `scale` cmZ1
              - ((a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * alpha * beta * z1_xi') `scale` cmS3
              + ((a_xi - f_xi) * alpha3) `scale` cmQk
              + ((one + delta) * (epsilon + f_xi) * (epsilon * (one + delta) + t_xi + delta * t_xi') * alpha4 + lagrange1_xi * alpha5) `scale` cmZ2
              - (z2_xi' * (epsilon * (one + delta) + h2_xi + delta * h1_xi') * alpha4) `scale` cmH1
              - zhX_xi `scale` (cmQlow + (xi^(n+2)) `scale` cmQmid + (xi^(2*n+4)) `scale` cmQhigh)

        -- Step 11: Compute F
        f = d
            + v `scale` cmA
            + vn 2 `scale` cmB
            + vn 3 `scale` cmC
            + vn 4 `scale` cmS1
            + vn 5 `scale` cmS2
            + vn 6 `scale` cmF
            + vn 7 `scale` cmT_zeta
            + vn 8 `scale` cmH2
            + eta `scale` cmZ1
            + (eta * v) `scale` cmT_zeta
            + (eta * vn 2) `scale` cmZ2
            + (eta * vn 3) `scale` cmH1

        -- Step 12: Compute E
        gen1 = pointGen @c1 @Bool @f1 @scalarField @pt1
        e = (
                negate r0 + v * a_xi + vn 2 * b_xi + vn 3 * c_xi + vn 4 * s1_xi + vn 5 * s2_xi + vn 6 * f_xi
                + vn 7 * t_xi + vn 8 * h2_xi + eta * z1_xi' + eta * v * t_xi' + eta * vn 2 * z2_xi' + eta * vn 3 * h1_xi'
            ) `scale` gen1

        -- Step 13: Compute the pairing
        pair = pairing @scalarField @g1 @g2 @gt
        gen2 = pointGen @c2 @Bool @f2 @scalarField @pt2
        p1 = pair (proof1 + eta `scale` proof2) h1
        p2 = pair (xi `scale` proof1 + (eta * xi * omega) `scale` proof2 + f - e) gen2
