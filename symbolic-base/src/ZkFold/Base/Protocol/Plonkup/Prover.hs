{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

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
import           Prelude                                             hiding (Num (..), Ord (..), drop, length, pi, sum,
                                                                      take, (!!), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, Natural, value)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (CompressedPoint, EllipticCurve (..), compress)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (polyVecDiv, polyVecInLagrangeBasis,
                                                                      polyVecLagrange, qr)
import           ZkFold.Base.Data.Vector                             ((!!))
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkupPolyExtended, PlonkupPolyExtendedLength)
import           ZkFold.Base.Protocol.Plonkup.Proof
import           ZkFold.Base.Protocol.Plonkup.Prover.Polynomials
import           ZkFold.Base.Protocol.Plonkup.Prover.Secret
import           ZkFold.Base.Protocol.Plonkup.Prover.Setup
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Testing                (PlonkupProverTestInfo (..))
import           ZkFold.Base.Protocol.Plonkup.Utils                  (sortByList)
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Ord

plonkupProve :: forall p i n l c1 c2 ts core .
    ( KnownNat n
    , KnownNat (PlonkupPolyExtendedLength n)
    , Foldable l
    , Ord (BooleanOf c1) (BaseField c1)
    , AdditiveGroup (BaseField c1)
    , Arithmetic (ScalarField c1)
    , ToTranscript ts Word8
    , ToTranscript ts (ScalarField c1)
    , ToTranscript ts (CompressedPoint c1)
    , FromTranscript ts (ScalarField c1)
    , CoreFunction c1 core
    ) => PlonkupProverSetup p i n l c1 c2 -> (PlonkupWitnessInput p i c1, PlonkupProverSecret c1) -> (PlonkupInput l c1, PlonkupProof c1, PlonkupProverTestInfo n c1)
plonkupProve PlonkupProverSetup {..}
        (PlonkupWitnessInput wExtra wInput, PlonkupProverSecret ps)
    = (PlonkupInput wPub, PlonkupProof {..}, PlonkupProverTestInfo {..})
    where
        (@) :: forall size . (KnownNat size) => PolyVec (ScalarField c1) size -> PolyVec (ScalarField c1) size -> PolyVec (ScalarField c1) size
        (@) a b = poly2vec $ polyMul @c1 @core (vec2poly a) (vec2poly b)

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

        PlonkupCircuitPolynomials {..} = polynomials
        secret i = ps !! (i -! 1)

        n = value @n
        zhX = polyVecZero @_ @n @(PlonkupPolyExtendedLength n)

        (w1, w2, w3) = witness relation wExtra wInput
        wPub = pubInput relation wExtra wInput

        w1X = polyVecInLagrangeBasis omega w1 :: PlonkupPolyExtended n c1
        w2X = polyVecInLagrangeBasis omega w2 :: PlonkupPolyExtended n c1
        w3X = polyVecInLagrangeBasis omega w3 :: PlonkupPolyExtended n c1

        -- Is this really correct?
        -- How is \(n\) related to the length of public input?
        pi  = toPolyVec @_ @n $ fromList $ foldMap (\x -> [negate x]) wPub
        piX = polyVecInLagrangeBasis omega pi  :: PlonkupPolyExtended n c1

        -- Round 1

        aX = polyVecLinear (secret 1) (secret 2) @ zhX + w1X :: PlonkupPolyExtended n c1
        bX = polyVecLinear (secret 3) (secret 4) @ zhX + w2X :: PlonkupPolyExtended n c1
        cX = polyVecLinear (secret 5) (secret 6) @ zhX + w3X :: PlonkupPolyExtended n c1

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

        fX = polyVecLinear (secret 7) (secret 8) @ zhX + polyVecInLagrangeBasis omega f_zeta :: PlonkupPolyExtended n c1

        s  = sortByList (toList f_zeta ++ toList t_zeta) (toList t_zeta)
        h1 = toPolyVec $ V.ifilter (\i _ -> odd i) $ fromList s  :: PolyVec (ScalarField c1) n
        h2 = toPolyVec $ V.ifilter (\i _ -> even i) $ fromList s :: PolyVec (ScalarField c1) n

        h1X = polyVecQuadratic (secret 9) (secret 10) (secret 11) @ zhX + polyVecInLagrangeBasis omega h1 :: PlonkupPolyExtended n c1
        h2X = polyVecLinear (secret 12) (secret 13) @ zhX + polyVecInLagrangeBasis omega h2 :: PlonkupPolyExtended n c1

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

        omegas  = toPolyVec $ V.iterateN (fromIntegral n) (* omega) omega
        omegas' = toPolyVec $ V.iterateN (fromIntegral $ value @(PlonkupPolyExtendedLength n)) (* omega) one

        cumprod :: PolyVec (ScalarField c1) n -> PolyVec (ScalarField c1) n
        cumprod = toPolyVec . V.scanl1' (*) . fromPolyVec

        rotR :: PolyVec (ScalarField c1) n -> PolyVec (ScalarField c1) n
        rotR p = toPolyVec $ V.drop (fromIntegral $ value @n -! 1) (fromPolyVec p) V.++ V.take (fromIntegral $ value @n -! 1) (fromPolyVec p)

        rotL :: PolyVec (ScalarField c1) n -> PolyVec (ScalarField c1) n
        rotL p = toPolyVec $ V.drop 1 (fromPolyVec p) V.++ V.take 1 (fromPolyVec p)

        -- TODO: check operation order
        grandProduct1 = rotR . cumprod $
                (w1 + (beta *. omegas) .+ gamma)
            .*. (w2 + ((beta * k1) *. omegas) .+ gamma)
            .*. (w3 + ((beta * k2) *. omegas) .+ gamma)
            ./. (w1 + (beta *. sigma1s) .+ gamma)
            ./. (w2 + (beta *. sigma2s) .+ gamma)
            ./. (w3 + (beta *. sigma3s) .+ gamma)
        z1X = polyVecQuadratic (secret 14) (secret 15) (secret 16) @ zhX + polyVecInLagrangeBasis omega grandProduct1 :: PlonkupPolyExtended n c1

        grandProduct2 = rotR . cumprod $
                (one + delta) *. (epsilon +. f_zeta)
            .*. ((epsilon * (one + delta)) +. t_zeta + delta *. rotL t_zeta)
            ./. ((epsilon * (one + delta)) +. h1 + delta *. h2)
            ./. ((epsilon * (one + delta)) +. h2 + delta *. rotL h1)
        z2X = polyVecQuadratic (secret 17) (secret 18) (secret 19) @ zhX + polyVecInLagrangeBasis omega grandProduct2 :: PlonkupPolyExtended n c1

        cmZ1 = gs `com` z1X
        cmZ2 = gs `com` z2X

        -- Round 4

        ts3 = ts2
            `transcript` compress cmZ1
            `transcript` compress cmZ2
        alpha  = challenge ts3
        alpha2 = alpha * alpha
        alpha3 = alpha2 * alpha
        alpha4 = alpha3 * alpha
        alpha5 = alpha4 * alpha

        gammaX   = scalePV gamma one
        deltaX   = scalePV delta one
        epsilonX = scalePV epsilon one
        qX = (
                (qmX @ aX @ bX + qlX @ aX + qrX @ bX + qoX @ cX + piX + qcX)
              + (aX + polyVecLinear beta gamma) @ (bX + polyVecLinear (beta * k1) gamma) @ (cX + polyVecLinear (beta * k2) gamma) @ z1X .* alpha
              - (aX + (beta *. s1X) + gammaX) @ (bX + (beta *. s2X) + gammaX) @ (cX + (beta *. s3X) + gammaX) @ (z1X .*. omegas') .* alpha
              + (z1X - one) @ polyVecLagrange @_ @n 1 omega .* alpha2
              + qkX @ (aX - fX) .* alpha3
              + z2X @ (one + deltaX) @ (epsilonX + fX) @ ((epsilonX @ (one + deltaX)) + tX + deltaX @ (tX .*. omegas')) .* alpha4
              - (z2X .*. omegas') @ ((epsilonX @ (one + deltaX)) + h1X + deltaX @ h2X) @ ((epsilonX @ (one + deltaX)) + h2X + deltaX @ (h1X .*. omegas')) .* alpha4
              + (z2X - one) @ polyVecLagrange @_ @n 1 omega .* alpha5
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

        a_xi    = aX `evalPolyVec` xi
        b_xi    = bX `evalPolyVec` xi
        c_xi    = cX `evalPolyVec` xi
        s1_xi   = s1X `evalPolyVec` xi
        s2_xi   = s2X `evalPolyVec` xi
        f_xi    = fX `evalPolyVec` xi
        t_xi    = tX `evalPolyVec` xi
        t_xi'   = tX `evalPolyVec` (xi * omega)
        z1_xi'  = z1X `evalPolyVec` (xi * omega)
        z2_xi'  = z2X `evalPolyVec` (xi * omega)
        h1_xi'  = h1X `evalPolyVec` (xi * omega)
        h2_xi   = h2X `evalPolyVec` xi
        lag1_xi = polyVecLagrange @_ @n @(PlonkupPolyExtendedLength n) 1 omega `evalPolyVec` xi
        l1_xi   = one // (scale n one * (xi - omega))

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
            `transcript` z1_xi'
            `transcript` z2_xi'
            `transcript` h1_xi'
            `transcript` h2_xi
        v = challenge ts5

        pi_xi = piX `evalPolyVec` xi
        zhX_xi = zhX `evalPolyVec` xi

        rX =
                qmX .* (a_xi * b_xi) + qlX .* a_xi + qrX .* b_xi + qoX .* c_xi + one .* pi_xi + qcX
              + alpha *. (((a_xi + beta * xi + gamma) * (b_xi + beta * k1 * xi + gamma) * (c_xi + beta * k2 * xi + gamma)) *. z1X
                        - ((a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * z1_xi') *. (one .* c_xi + beta *. s3X + one .* gamma)
                    )
              + (alpha2 * lag1_xi) *. (z1X - one)
              + (alpha3 * (a_xi - f_xi)) *. qkX
              + alpha4 *. (((one + delta) * (epsilon + f_xi) * ((epsilon * (one + delta)) + t_xi + delta * t_xi')) *. z2X
                        - (z2_xi' * ((epsilon * (one + delta)) + h2_xi + delta * h1_xi')) *. (one .* (epsilon * (one + delta)) + h1X + one .* (delta * h2_xi))
                    )
              + (alpha5 * lag1_xi) *. (z2X - one)
              - zhX_xi *. (qlowX + (xi^(n+2)) *. qmidX + (xi^(2*n+4)) *. qhighX)

        vn i = v ^ (i :: Natural)

        proofX1 = (
                  rX
                + (vn 1 *. (aX - (a_xi *. one)))
                + (vn 2 *. (bX - (b_xi *. one)))
                + (vn 3 *. (cX - (c_xi *. one)))
                + (vn 4 *. (s1X - (s1_xi *. one)))
                + (vn 5 *. (s2X - (s2_xi *. one)))
                + (vn 6 *. (fX - (f_xi *. one)))
                + (vn 7 *. (tX - (t_xi *. one)))
                + (vn 8 *. (h2X - (h2_xi *. one)))
            ) `polyVecDiv` polyVecLinear one (negate xi)
        proofX2 = (
                  z1X - (z1_xi' *. one)
                + (vn 1 *. (tX - (t_xi' *. one)))
                + (vn 2 *. (z2X - (z2_xi' *. one)))
                + (vn 3 *. (h1X - (h1_xi' *. one)))
            ) `polyVecDiv` polyVecLinear one (negate (xi * omega))

        proof1 = gs `com` proofX1
        proof2 = gs `com` proofX2
