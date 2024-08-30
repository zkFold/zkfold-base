{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Protocol.Plonkup (
    module ZkFold.Base.Protocol.Plonkup.Internal,
    Plonk(..),
    plonkPermutation,
    plonkCircuitPolynomials,
    plonkVerifierInput
) where

import           Data.Functor                                        ((<&>))
import           Data.Functor.Rep                                    (Representable (..))
import qualified Data.Map                                            as Map
import qualified Data.Vector                                         as V
import           GHC.Generics                                        (Par1)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P hiding (length)
import           Test.QuickCheck                                     (Arbitrary (..), Gen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations              (fromPermutation)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing (..), Point,
                                                                      PointCompressed, compress)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector (..), fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Base.Protocol.Plonkup.Internal
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Setup
import           ZkFold.Base.Protocol.Plonkup.Verifier
import           ZkFold.Symbolic.Compiler                            (ArithmeticCircuitTest (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

instance forall i n l c1 c2 t core . (KnownNat i, KnownNat n, KnownNat l, Arithmetic (ScalarField c1), Arbitrary (ScalarField c1),
        Witness (Plonk i n l c1 c2 t) ~ (PlonkWitnessInput i c1, PlonkProverSecret c1), NonInteractiveProof (Plonk i n l c1 c2 t) core) => Arbitrary (NonInteractiveProofTestData (Plonk i n l c1 c2 t) core) where
    arbitrary = do
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest (ScalarField c1) (Vector i) Par1)
        vecPubInp <- genSubset (getAllVars ac) (value @l)
        let (omega, k1, k2) = getParams $ value @n
        pl <- Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
        secret <- arbitrary
        return $ TestData pl (PlonkWitnessInput wi (witnessGenerator ac wi), secret)

plonkPermutation :: forall i n l c1 c2 t .
    (KnownNat n, FiniteField (ScalarField c1)) => Plonk i n l c1 c2 t -> PlonkupRelation n i (ScalarField c1) -> PlonkPermutation n c1
plonkPermutation (Plonk omega k1 k2 _ _ _) PlonkupRelation {..} = PlonkPermutation {..}
    where
        f i = case (i-!1) `div` value @n of
            0 -> omega^i
            1 -> k1 * (omega^i)
            2 -> k2 * (omega^i)
            _ -> error "setup: invalid index"

        s = fromList $ map f $ fromPermutation @(PlonkPermutationSize n) sigma
        s1 = toPolyVec $ V.take (fromIntegral $ value @n) s
        s2 = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ value @n) s
        s3 = toPolyVec $ V.take (fromIntegral $ value @n) $ V.drop (fromIntegral $ 2 * value @n) s

plonkCircuitPolynomials :: forall i n l c1 c2 t .
    (KnownNat n, KnownNat (PlonkPolyExtendedLength n), Eq (ScalarField c1), Field (ScalarField c1))
    => Plonk i n l c1 c2 t
    -> PlonkPermutation n c1
    -> PlonkupRelation n i (ScalarField c1)
    -> PlonkCircuitPolynomials n c1
plonkCircuitPolynomials
   (Plonk omega _ _ _ _ _)
   PlonkPermutation {..}
   PlonkupRelation {..} = PlonkCircuitPolynomials {..}
    where
        qm     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qM
        ql     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qL
        qr     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qR
        qo     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qO
        qc     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qC
        qk     = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega qK
        sigma1 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega s1
        sigma2 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega s2
        sigma3 = polyVecInLagrangeBasis @(ScalarField c1) @n @(PlonkPolyExtendedLength n) omega s3

plonkVerifierInput :: Field (ScalarField c) => Vector l (ScalarField c) -> PlonkInput l c
plonkVerifierInput input = PlonkInput $ fmap negate input

instance forall i n l c1 c2 t plonk f g1 core.
        ( Plonk i n l c1 c2 t ~ plonk
        , ScalarField c1 ~ f
        , Point c1 ~ g1
        , KnownNat n
        , KnownNat l
        , KnownNat i
        , KnownNat (PlonkPermutationSize n)
        , KnownNat (PlonkPolyExtendedLength n)
        , Arithmetic f
        , Ord (BaseField c1)
        , AdditiveGroup (BaseField c1)
        , Pairing c1 c2
        , ToTranscript t (ScalarField c1)
        , ToTranscript t (PointCompressed c1)
        , FromTranscript t (ScalarField c1)
        , CoreFunction c1 core
        ) => NonInteractiveProof (Plonk i n l c1 c2 t) core where
    type Transcript (Plonk i n l c1 c2 t)  = t
    type SetupProve (Plonk i n l c1 c2 t)  = PlonkupProverSetup i n l c1 c2
    type SetupVerify (Plonk i n l c1 c2 t) = PlonkupVerifierSetup i n l c1 c2
    type Witness (Plonk i n l c1 c2 t)     = (PlonkWitnessInput i c1, PlonkProverSecret c1)
    type Input (Plonk i n l c1 c2 t)       = PlonkInput l c1
    type Proof (Plonk i n l c1 c2 t)       = PlonkProof c1

    setupProve :: plonk -> SetupProve plonk
    setupProve plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupProverSetup {..}

    setupVerify :: plonk -> SetupVerify plonk
    setupVerify plonk =
        let PlonkupSetup {..} = plonkupSetup @_ @_ @_ @c1 @_ @_ @core plonk
        in PlonkupVerifierSetup {..}

    prove :: SetupProve plonk -> Witness plonk -> (Input plonk, Proof plonk)
    prove PlonkupProverSetup {..}
          (PlonkWitnessInput wInput wNewVars, PlonkProverSecret {..})
        = (PlonkInput wPub, PlonkProof {..})
        where
            PlonkCircuitPolynomials {..} = polynomials

            n = value @n
            zH = polyVecZero @f @n @(PlonkPolyExtendedLength n)

            (w1, w2, w3) = wmap relation wInput wNewVars

            wPub = iPub <&> negate . \case
              InVar j -> index wInput j
              NewVar j -> wNewVars Map.! j

            pubPoly = polyVecInLagrangeBasis omega $ toPolyVec @f @n $ fromList $ fromVector wPub

            a = polyVecLinear b2 b1 * zH + polyVecInLagrangeBasis omega w1
            b = polyVecLinear b4 b3 * zH + polyVecInLagrangeBasis omega w2
            c = polyVecLinear b6 b5 * zH + polyVecInLagrangeBasis omega w3

            com = msm @c1 @core
            cmA = gs `com` a
            cmB = gs `com` b
            cmC = gs `com` c

            (beta, ts) = challenge $ mempty
                `transcript` compress cmA
                `transcript` compress cmB
                `transcript` compress cmC
            (gamma, ts') = challenge ts

            omegas  = toPolyVec $ V.iterateN (fromIntegral n) (* omega) omega
            omegas' =  V.iterateN (V.length (fromPolyVec z) P.+ 1) (* omega) one
            zs1 = polyVecGrandProduct w1 omegas sigma1s beta gamma
            zs2 = polyVecGrandProduct w2 (scalePV k1 omegas) sigma2s beta gamma
            zs3 = polyVecGrandProduct w3 (scalePV k2 omegas) sigma3s beta gamma
            gp = rewrapPolyVec (V.zipWith (*) (V.zipWith (*) (fromPolyVec zs1) (fromPolyVec zs2))) zs3
            z  = polyVecQuadratic b9 b8 b7 * zH + polyVecInLagrangeBasis @f @n @(PlonkPolyExtendedLength n) omega gp
            zo = toPolyVec $ V.zipWith (*) (fromPolyVec z) omegas'
            cmZ = gs `com` z

            (alpha, ts'') = challenge $ ts' `transcript` compress cmZ :: (f, Transcript plonk)

            t1  = a * b * qm + a * ql + b * qr + c * qo + pubPoly + qc
            t2  = (a + polyVecLinear gamma beta)
                * (b + polyVecLinear gamma (beta * k1))
                * (c + polyVecLinear gamma (beta * k2))
                * z
            t3  = (a + scalePV beta sigma1 + scalePV gamma one)
                * (b + scalePV beta sigma2 + scalePV gamma one)
                * (c + scalePV beta sigma3 + scalePV gamma one)
                * zo
            t4 = (z - one) * polyVecLagrange @f @n @(PlonkPolyExtendedLength n) 1 omega
            t = (t1 + scalePV alpha (t2 - t3) + scalePV (alpha * alpha) t4) `polyVecDiv` zH

            t_lo'  = toPolyVec $ V.take (fromIntegral n) $ fromPolyVec t
            t_mid' = toPolyVec $ V.take (fromIntegral n) $ V.drop (fromIntegral n) $ fromPolyVec t
            t_hi'  = toPolyVec $ V.drop (fromIntegral $ 2*n) $ fromPolyVec t
            t_lo   = t_lo' + scalePV b10 (polyVecZero @f @n @(PlonkPolyExtendedLength n) + one)
            t_mid  = t_mid' + scalePV b11 (polyVecZero @f @n @(PlonkPolyExtendedLength n) + one) - scalePV b10 one
            t_hi   = t_hi' - scalePV b11 one
            cmT1   = gs `com` t_lo
            cmT2   = gs `com` t_mid
            cmT3   = gs `com` t_hi

            (xi, ts''') = challenge $ ts''
                `transcript` compress cmT1
                `transcript` compress cmT2
                `transcript` compress cmT3

            a_xi  = evalPolyVec a xi
            b_xi  = evalPolyVec b xi
            c_xi  = evalPolyVec c xi
            s1_xi = evalPolyVec sigma1 xi
            s2_xi = evalPolyVec sigma2 xi
            z_xi  = evalPolyVec z (xi * omega)
            l1_xi_mul = one // (scale n one * (xi - omega))

            (v, _) = challenge $ ts'''
                `transcript` a_xi
                `transcript` b_xi
                `transcript` c_xi
                `transcript` s1_xi
                `transcript` s2_xi
                `transcript` z_xi

            lagrange1_xi = polyVecLagrange @f @n @(PlonkPolyExtendedLength n) 1 omega `evalPolyVec` xi
            zH_xi = zH `evalPolyVec` xi
            r   = scalePV (a_xi * b_xi) qm
                + scalePV a_xi ql
                + scalePV b_xi qr
                + scalePV c_xi qo
                + scalePV (pubPoly `evalPolyVec` xi) one
                + qc
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
                        ) (scalePV beta sigma3 + scalePV (c_xi + gamma) one)
                    )
                + scalePV (alpha * alpha * lagrange1_xi) (z - one)
                - scalePV zH_xi (scalePV (xi^(2 * n)) t_hi + scalePV (xi^n) t_mid + t_lo)

            proof1Poly = (r
                    + scalePV v (a - scalePV a_xi one)
                    + scalePV (v * v) (b - scalePV b_xi one)
                    + scalePV (v * v * v) (c - scalePV c_xi one)
                    + scalePV (v * v * v * v) (sigma1 - scalePV s1_xi one)
                    + scalePV (v * v * v * v * v) (sigma2 - scalePV s2_xi one)
                ) `polyVecDiv` polyVecLinear (negate xi) one

            proof2Poly = (z - scalePV z_xi one) `polyVecDiv` toPolyVec [negate (xi * omega), one]

            proof1 = gs `com` proof1Poly
            proof2 = gs `com` proof2Poly

    verify :: SetupVerify plonk -> Input plonk -> Proof plonk -> Bool
    verify
        PlonkupVerifierSetup {..}
        (PlonkInput wPub)
        (PlonkProof cmA cmB cmC cmZ cmT1 cmT2 cmT3 proof1 proof2 a_xi b_xi c_xi s1_xi s2_xi z_xi _) = p1 == p2
        where
            PlonkCircuitCommitments {..} = commitments

            n = value @n

            (beta, ts) = challenge $ mempty
                `transcript` compress cmA
                `transcript` compress cmB
                `transcript` compress cmC :: (f, Transcript plonk)
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

            zH_xi        = polyVecZero @f @n @(PlonkPolyExtendedLength n) `evalPolyVec` xi
            lagrange1_xi = polyVecLagrange @f @n @(PlonkPolyExtendedLength n) 1 omega `evalPolyVec` xi
            pubPoly_xi   = polyVecInLagrangeBasis @f @n @(PlonkPolyExtendedLength n) omega (toPolyVec $ fromList $ fromVector wPub) `evalPolyVec` xi

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
