{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier
    ( module ZkFold.Base.Protocol.Plonkup.Verifier.Commitments
    , module ZkFold.Base.Protocol.Plonkup.Verifier.Setup
    , plonkupVerify
    ) where

import qualified Data.Vector                                         as V
import           Data.Word                                           (Word8)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), Ord (..), drop, length, sum,
                                                                      take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, Natural, value)
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (polyVecDiv, polyVecInLagrangeBasis,
                                                                      polyVecLagrange, qr)
import           ZkFold.Base.Protocol.NonInteractiveProof            hiding (verify)
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Verifier.Commitments
import           ZkFold.Base.Protocol.Plonkup.Verifier.Setup
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Ord

plonkupVerify :: forall p i n l c1 c2 ts core .
    ( KnownNat n
    , KnownNat (PlonkupPolyExtendedLength n)
    , Foldable l
    , Pairing c1 c2
    , Ord (BooleanOf c1) (BaseField c1)
    , AdditiveGroup (BaseField c1)
    , Arithmetic (ScalarField c1)
    , ToTranscript ts Word8
    , ToTranscript ts (ScalarField c1)
    , ToTranscript ts (CompressedPoint c1)
    , FromTranscript ts (ScalarField c1)
    , CoreFunction c1 core
    ) => PlonkupVerifierSetup p i n l c1 c2 -> PlonkupInput l c1 -> PlonkupProof c1 -> Bool
plonkupVerify
    PlonkupVerifierSetup {..}
    (PlonkupInput wPub)
    (PlonkupProof {..}) = p1 == p2
    where
        PlonkupCircuitCommitments {..} = commitments

        n = value @n

        -- Step 4: Compute challenges

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
        zhX_xi = polyVecZero @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) `evalPolyVec` xi :: ScalarField c1

        -- Step 6: Compute Lagrange polynomial evaluation
        lagrange1_xi = polyVecLagrange @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) 1 omega `evalPolyVec` xi

        -- Step 7: Compute public polynomial evaluation
        pi_xi = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkupPolyExtendedLength n) omega
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
        d =
                (a_xi * b_xi) `mul` cmQm + a_xi `mul` cmQl + b_xi `mul` cmQr + c_xi `mul` cmQo + cmQc
              + ((a_xi + beta * xi + gamma) * (b_xi + beta * k1 * xi + gamma) * (c_xi + beta * k2 * xi + gamma) * alpha + lagrange1_xi * alpha2) `mul` cmZ1
              - ((a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * alpha * beta * z1_xi') `mul` cmS3
              + ((a_xi - f_xi) * alpha3) `mul` cmQk
              + ((one + delta) * (epsilon + f_xi) * (epsilon * (one + delta) + t_xi + delta * t_xi') * alpha4 + lagrange1_xi * alpha5) `mul` cmZ2
              - (z2_xi' * (epsilon * (one + delta) + h2_xi + delta * h1_xi') * alpha4) `mul` cmH1
              - zhX_xi `mul` (cmQlow + (xi^(n+2)) `mul` cmQmid + (xi^(2*n+4)) `mul` cmQhigh)

        -- Step 11: Compute F
        f = d
            + v `mul` cmA
            + vn 2 `mul` cmB
            + vn 3 `mul` cmC
            + vn 4 `mul` cmS1
            + vn 5 `mul` cmS2
            + vn 6 `mul` cmF
            + vn 7 `mul` cmT_zeta
            + vn 8 `mul` cmH2
            + eta `mul` cmZ1
            + (eta * v) `mul` cmT_zeta
            + (eta * vn 2) `mul` cmZ2
            + (eta * vn 3) `mul` cmH1

        -- Step 12: Compute E
        e = (
                negate r0 + v * a_xi + vn 2 * b_xi + vn 3 * c_xi + vn 4 * s1_xi + vn 5 * s2_xi + vn 6 * f_xi
                + vn 7 * t_xi + vn 8 * h2_xi + eta * z1_xi' + eta * v * t_xi' + eta * vn 2 * z2_xi' + eta * vn 3 * h1_xi'
            ) `mul` pointGen

        -- Step 13: Compute the pairing
        p1 = pairing (proof1 + eta `mul` proof2) h1
        p2 = pairing (xi `mul` proof1 + (eta * xi * omega) `mul` proof2 + f - e) (pointGen @c2)

        polyVecDiv :: forall c size . (c ~ ScalarField c1, KnownNat size) =>PolyVec c size -> PolyVec c size -> PolyVec c size
        polyVecDiv l r = poly2vec $ fst $ (polyQr @c1 @core) (vec2poly l) (vec2poly r)

        polyVecLagrange :: forall c m size . (c ~ ScalarField c1, KnownNat m, KnownNat size) =>
            Natural -> c -> PolyVec c size
        polyVecLagrange i omega' = scalePV (omega'^i // fromConstant (value @m)) $ (polyVecZero @c @m @size - one) `polyVecDiv` polyVecLinear one (negate $ omega'^i)

        polyVecInLagrangeBasis :: forall c m size . (c ~ ScalarField c1, KnownNat m, KnownNat size) =>
            c -> PolyVec c m -> PolyVec c size
        polyVecInLagrangeBasis omega' cs =
            let ls = fmap (\i -> polyVecLagrange @c @m @size i omega') (V.generate (V.length (fromPolyVec cs)) (fromIntegral . succ))
            in sum $ V.zipWith scalePV (fromPolyVec cs) ls
