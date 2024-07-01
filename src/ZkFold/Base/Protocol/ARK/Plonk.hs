{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Plonk where

import qualified Data.Map                                            as Map
import           Data.Maybe                                          (fromJust)
import qualified Data.Vector                                         as V
import           GHC.Natural                                         (naturalToInteger)
import           GHC.Num                                             (integerToInt)
import           Numeric.Natural                                     (Natural)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), div, drop, length, replicate,
                                                                      sum, take, (!!), (/), (^))
import qualified Prelude                                             as P
import           Test.QuickCheck                                     (Arbitrary (..), Gen, chooseInteger, vector)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                     (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations              (fromPermutation)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381         (BLS12_381_G1, BLS12_381_G2, BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..), Pairing (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate          hiding (qr)
import           ZkFold.Base.Data.Vector                             (Vector (..), fromVector)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal             (getParams)
import           ZkFold.Base.Protocol.ARK.Plonk.Relation             (PlonkRelation (..), toPlonkRelation)
import           ZkFold.Base.Protocol.Commitment.KZG                 (com)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                                      ((!))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit (..), Arithmetic, inputVariables)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance (arbitrary')

-- TODO (Issue #25): make this module generic in the elliptic curve with pairing

type F = Zp BLS12_381_Scalar
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

{-
    NOTE: we need to parametrize the type of transcripts because we use BuiltinByteString on-chain and ByteString off-chain.
    Additionally, we don't want this library to depend on Cardano libraries.
-}

data Plonk (d :: Natural) (n :: Natural) t = Plonk F F F (Vector n Natural) (ArithmeticCircuit 1 F) F
    deriving (Show)
-- TODO (Issue #25): make a proper implementation of Arbitrary
instance (KnownNat d) => Arbitrary (Plonk d n t) where
    arbitrary = do
        let nP = ceiling @Double . logBase 2.0 . fromIntegral $ value @d
        let (omega, k1, k2) = getParams nP
        ac <- arbitrary' (toInteger nP)
        Plonk omega k1 k2 (Vector [1..nP]) ac <$> arbitrary

type PlonkPermutationSize d = 3 * d

-- TODO (Issue #25): check that the extended polynomials are of the right size
type PlonkMaxPolyDegree d = 4 * d + 7

type PlonkPolyExtended d = PolyVec F (PlonkMaxPolyDegree d)

data PlonkSetupParamsProve = PlonkSetupParamsProve {
        omega' :: F,
        k1'    :: F,
        k2'    :: F,
        gs'    :: V.Vector G1,
        h0'    :: G2,
        h1'    :: G2,
        iPub'  :: V.Vector Natural
    }
    deriving (Show)

data PlonkSetupParamsVerify = PlonkSetupParamsVerify {
        omega :: F,
        k1    :: F,
        k2    :: F,
        g0    :: G1,
        h0    :: G2,
        h1    :: G2,
        pow   :: Integer
    }
    deriving (Show)

data PlonkPermutation d = PlonkPermutation {
        s1 :: PolyVec F d,
        s2 :: PolyVec F d,
        s3 :: PolyVec F d
    }
    deriving (Show)

data PlonkCircuitPolynomials d = PlonkCircuitPolynomials {
        ql     :: PlonkPolyExtended d,
        qr     :: PlonkPolyExtended d,
        qo     :: PlonkPolyExtended d,
        qm     :: PlonkPolyExtended d,
        qc     :: PlonkPolyExtended d,
        sigma1 :: PlonkPolyExtended d,
        sigma2 :: PlonkPolyExtended d,
        sigma3 :: PlonkPolyExtended d
    }
    deriving (Show)

data PlonkCircuitCommitments = PlonkCircuitCommitments {
        cmQl :: G1,
        cmQr :: G1,
        cmQo :: G1,
        cmQm :: G1,
        cmQc :: G1,
        cmS1 :: G1,
        cmS2 :: G1,
        cmS3 :: G1
    }
    deriving (Show)

newtype PlonkWitnessMap d = PlonkWitnessMap (Map.Map Natural F -> (PolyVec F d, PolyVec F d, PolyVec F d))

newtype PlonkWitnessInput = PlonkWitnessInput (Map.Map Natural F)
-- TODO (Issue #25): make a proper implementation of Show
instance Arbitrary PlonkWitnessInput where
    arbitrary = do
        keysLen <- ceiling @Double . logBase 2.0 . fromIntegral <$> chooseInteger (0, 100)
        let keys = [0..keysLen]
        values <- vector (integerToInt $ naturalToInteger keysLen) :: Gen [F]
        let wi = Map.fromList $ zip keys values
        return (PlonkWitnessInput wi)

instance Show PlonkWitnessInput where
    show (PlonkWitnessInput m) = "Witness Input: " ++ show m

data (Arithmetic a, KnownNat n) => ACandWitness n a = ACandWitness
    {
        arithmeticCircuit :: ArithmeticCircuit n a
        , witnessInput    :: PlonkWitnessInput
    }

instance (Arithmetic a, KnownNat n) => Arbitrary (ACandWitness n a) where
    arbitrary :: Gen (ACandWitness n a)
    arbitrary = do
        ac <- arbitrary
        let keys = inputVariables ac
        let len = last keys
        values <- vector (integerToInt $ naturalToInteger len)
        let wi = fromList $ zip keys values
        return ACandWitness {
            arithmeticCircuit = ac
            , witnessInput = PlonkWitnessInput wi
            }

data PlonkProverSecret = PlonkProverSecret F F F F F F F F F F F
    deriving (Show)
instance Arbitrary PlonkProverSecret where
    arbitrary = PlonkProverSecret <$>
        arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

newtype PlonkInput = PlonkInput (V.Vector F)
    deriving (Show)

instance Arbitrary PlonkInput where
    arbitrary = do
        PlonkInput . fromList <$> arbitrary

data PlonkProof = PlonkProof G1 G1 G1 G1 G1 G1 G1 G1 G1 F F F F F F
    deriving (Show)

plonkPermutation :: forall d n t .
    (KnownNat d) => Plonk d n t -> PlonkRelation d n F -> PlonkPermutation d
plonkPermutation (Plonk omega k1 k2 _ _ _) PlonkRelation {..} = PlonkPermutation {..}
    where
        s = fromPermutation @(PlonkPermutationSize d) sigma

        f i = case (i-!1) `div` value @d of
            0 -> omega^i
            1 -> k1 * (omega^i)
            2 -> k2 * (omega^i)
            _ -> error "setup: invalid index"

        s' = fromList $ map f s
        s1 = toPolyVec $ V.take (fromIntegral $ value @d) s'
        s2 = toPolyVec $ V.take (fromIntegral $ value @d) $ V.drop (fromIntegral $ value @d) s'
        s3 = toPolyVec $ V.take (fromIntegral $ value @d) $ V.drop (fromIntegral $ 2 * value @d) s'

plonkCircuitPolynomials :: forall d n t .
    (KnownNat d, KnownNat (PlonkMaxPolyDegree d))
    => Plonk d n t
    -> PlonkPermutation d
    -> PlonkRelation d n F
    -> PlonkCircuitPolynomials d
plonkCircuitPolynomials
   (Plonk omega _ _ _ _ _)
   PlonkPermutation {..}
   PlonkRelation {..} = PlonkCircuitPolynomials {..}
    where
        qm     = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega qM
        ql     = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega qL
        qr     = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega qR
        qo     = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega qO
        qc     = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega qC
        sigma1 = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega s1
        sigma2 = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega s2
        sigma3 = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega s3

plonkVerifierInput :: Vector n F -> PlonkInput
plonkVerifierInput input = PlonkInput $ fromList $ map negate $ fromVector input

instance forall d n t .
        (KnownNat d,
         KnownNat n,
         KnownNat (PlonkPermutationSize d),
         KnownNat (PlonkMaxPolyDegree d),
         ToTranscript t F,
         ToTranscript t G1,
         FromTranscript t F) => NonInteractiveProof (Plonk d n t) where
    type Transcript (Plonk d n t)  = t
    type SetupProve (Plonk d n t)  = (PlonkSetupParamsProve, PlonkPermutation d, PlonkCircuitPolynomials d, PlonkWitnessMap d)
    type SetupVerify (Plonk d n t) = (PlonkSetupParamsVerify, PlonkCircuitCommitments)
    type Witness (Plonk d n t)     = (PlonkWitnessInput, PlonkProverSecret)
    type Input (Plonk d n t)       = PlonkInput
    type Proof (Plonk d n t)       = PlonkProof

    setupProve :: Plonk d n t -> SetupProve (Plonk d n t)
    setupProve plonk@(Plonk omega' k1' k2' iPub ac x) =
        (PlonkSetupParamsProve {..}, PlonkPermutation {..}, PlonkCircuitPolynomials {..}, PlonkWitnessMap $ wmap pr)
        where
            d     = value @d + 6
            xs    = fromList $ map (x^) [0..d-!1]
            gs'   = fmap (`mul` gen) xs
            h0'   = gen
            h1'   = x `mul` gen
            iPub' = fromList . fromVector $ iPub

            pr    = fromJust $ toPlonkRelation @d @n @F iPub ac

            perm@PlonkPermutation {..}   = plonkPermutation plonk pr
            PlonkCircuitPolynomials {..} = plonkCircuitPolynomials plonk perm pr

    setupVerify :: Plonk d n t -> SetupVerify (Plonk d n t)
    setupVerify plonk@(Plonk omega k1 k2 iPub ac x) = (PlonkSetupParamsVerify {..}, PlonkCircuitCommitments {..})
        where
            d = value @d + 6
            xs = fromList $ map (x^) [0..d-!1]
            gs = fmap (`mul` gen) xs
            g0 = V.head gs
            h0 = gen
            h1 = x `mul` gen
            pow = floor @Double . logBase 2.0 . fromIntegral $ value @d

            pr   = fromJust $ toPlonkRelation @d @n @F iPub ac
            perm = plonkPermutation plonk pr
            PlonkCircuitPolynomials {..} = plonkCircuitPolynomials plonk perm pr

            cmQl = gs `com` ql
            cmQr = gs `com` qr
            cmQo = gs `com` qo
            cmQm = gs `com` qm
            cmQc = gs `com` qc
            cmS1 = gs `com` sigma1
            cmS2 = gs `com` sigma2
            cmS3 = gs `com` sigma3

    prove :: SetupProve (Plonk d n t) -> Witness (Plonk d n t) -> (Input (Plonk d n t), Proof (Plonk d n t))
    prove (PlonkSetupParamsProve {..}, PlonkPermutation {..}, PlonkCircuitPolynomials {..}, PlonkWitnessMap wmap)
          (PlonkWitnessInput wInput, PlonkProverSecret b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11)
        = (PlonkInput wPub, PlonkProof cmA cmB cmC cmZ cmT1 cmT2 cmT3 proof1 proof2 a_xi b_xi c_xi s1_xi s2_xi z_xi)
        where
            d = value @d
            zH = polyVecZero @F @d @(PlonkMaxPolyDegree d)

            (w1, w2, w3) = wmap wInput

            wPub = fmap (negate . (wInput !)) iPub'

            pubPoly = polyVecInLagrangeBasis omega' $ toPolyVec @F @d wPub

            a = polyVecLinear b2 b1 * zH + polyVecInLagrangeBasis omega' w1
            b = polyVecLinear b4 b3 * zH + polyVecInLagrangeBasis omega' w2
            c = polyVecLinear b6 b5 * zH + polyVecInLagrangeBasis omega' w3

            cmA = gs' `com` a
            cmB = gs' `com` b
            cmC = gs' `com` c

            (beta, ts) = challenge $ mempty
                `transcript` cmA
                `transcript` cmB
                `transcript` cmC
            (gamma, ts') = challenge ts

            omegas  = toPolyVec $ V.iterateN (fromIntegral d) (* omega') omega'
            omegas' =  V.iterateN (V.length (fromPolyVec z) P.+ 1) (* omega') one
            zs1 = polyVecGrandProduct w1 omegas s1 beta gamma
            zs2 = polyVecGrandProduct w2 (scalePV k1' omegas) s2 beta gamma
            zs3 = polyVecGrandProduct w3 (scalePV k2' omegas) s3 beta gamma
            gp = rewrapPolyVec (V.zipWith (*) (V.zipWith (*) (fromPolyVec zs1) (fromPolyVec zs2))) zs3
            z  = polyVecQuadratic b9 b8 b7 * zH + polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega' gp
            zo = toPolyVec $ V.zipWith (*) (fromPolyVec z) omegas'
            cmZ = gs' `com` z

            (alpha, ts'') = challenge $ ts' `transcript` cmZ :: (F, Transcript (Plonk d n t))

            t1  = a * b * qm + a * ql + b * qr + c * qo + pubPoly + qc
            t2  = (a + polyVecLinear gamma beta)
                * (b + polyVecLinear gamma (beta * k1'))
                * (c + polyVecLinear gamma (beta * k2'))
                * z
            t3  = (a + scalePV beta sigma1 + scalePV gamma one)
                * (b + scalePV beta sigma2 + scalePV gamma one)
                * (c + scalePV beta sigma3 + scalePV gamma one)
                * zo
            t4 = (z - one) * polyVecLagrange @F @d @(PlonkMaxPolyDegree d) 1 omega'
            t = (t1 + scalePV alpha (t2 - t3) + scalePV (alpha * alpha) t4) `polyVecDiv` zH

            t_lo'  = toPolyVec $ V.take (fromIntegral d) $ fromPolyVec t
            t_mid' = toPolyVec $ V.take (fromIntegral d) $ V.drop (fromIntegral d) $ fromPolyVec t
            t_hi'  = toPolyVec $ V.drop (fromIntegral $ 2*d) $ fromPolyVec t
            t_lo   = t_lo' + scalePV b10 (polyVecZero @F @d @(PlonkMaxPolyDegree d) + one)
            t_mid  = t_mid' + scalePV b11 (polyVecZero @F @d @(PlonkMaxPolyDegree d) + one) - scalePV b10 one
            t_hi   = t_hi' - scalePV b11 one
            cmT1   = gs' `com` t_lo
            cmT2   = gs' `com` t_mid
            cmT3   = gs' `com` t_hi

            (xi, ts''') = challenge $ ts''
                `transcript` cmT1
                `transcript` cmT2
                `transcript` cmT3

            a_xi  = evalPolyVec a xi
            b_xi  = evalPolyVec b xi
            c_xi  = evalPolyVec c xi
            s1_xi = evalPolyVec sigma1 xi
            s2_xi = evalPolyVec sigma2 xi
            z_xi  = evalPolyVec z (xi * omega')

            (v, _) = challenge $ ts'''
                `transcript` a_xi
                `transcript` b_xi
                `transcript` c_xi
                `transcript` s1_xi
                `transcript` s2_xi
                `transcript` z_xi

            lagrange1_xi = polyVecLagrange @F @d @(PlonkMaxPolyDegree d) 1 omega' `evalPolyVec` xi
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
                        * (b_xi + beta * k1' * xi + gamma)
                        * (c_xi + beta * k2' * xi + gamma)
                        ) z
                    - scalePV (
                          (a_xi + beta * s1_xi + gamma)
                        * (b_xi + beta * s2_xi + gamma)
                        * z_xi
                        ) (scalePV beta sigma3 + scalePV (c_xi + gamma) one)
                    )
                + scalePV (alpha * alpha * lagrange1_xi) (z - one)
                - scalePV zH_xi (scalePV (xi^(2 * d)) t_hi + scalePV (xi^d) t_mid + t_lo)

            proof1Poly = (r
                    + scalePV v (a - scalePV a_xi one)
                    + scalePV (v * v) (b - scalePV b_xi one)
                    + scalePV (v * v * v) (c - scalePV c_xi one)
                    + scalePV (v * v * v * v) (sigma1 - scalePV s1_xi one)
                    + scalePV (v * v * v * v * v) (sigma2 - scalePV s2_xi one)
                ) `polyVecDiv` polyVecLinear (negate xi) one

            proof2Poly = (z - scalePV z_xi one) `polyVecDiv` toPolyVec [negate (xi * omega'), one]

            proof1 = gs' `com` proof1Poly
            proof2 = gs' `com` proof2Poly

    verify :: SetupVerify (Plonk d n t) -> Input (Plonk d n t) -> Proof (Plonk d n t) -> Bool
    verify
        (PlonkSetupParamsVerify {..}, PlonkCircuitCommitments {..})
        (PlonkInput wPub)
        (PlonkProof cmA cmB cmC cmZ cmT1 cmT2 cmT3 proof1 proof2 a_xi b_xi c_xi s1_xi s2_xi z_xi) = p1 == p2
        where
            n = value @d

            (beta, ts) = challenge $ mempty
                `transcript` cmA
                `transcript` cmB
                `transcript` cmC :: (F, Transcript (Plonk d n t))
            (gamma, ts') = challenge ts

            (alpha, ts'') = challenge $ ts' `transcript` cmZ

            (xi, ts''') = challenge $ ts''
                `transcript` cmT1
                `transcript` cmT2
                `transcript` cmT3

            (v, ts'''') = challenge $ ts'''
                `transcript` a_xi
                `transcript` b_xi
                `transcript` c_xi
                `transcript` s1_xi
                `transcript` s2_xi
                `transcript` z_xi

            (u, _) = challenge $ ts''''
                `transcript` proof1
                `transcript` proof2

            zH_xi        = polyVecZero @F @d @(PlonkMaxPolyDegree d) `evalPolyVec` xi
            lagrange1_xi = polyVecLagrange @F @d @(PlonkMaxPolyDegree d) 1 omega `evalPolyVec` xi
            pubPoly_xi   = polyVecInLagrangeBasis @F @d @(PlonkMaxPolyDegree d) omega (toPolyVec wPub) `evalPolyVec` xi

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
                - r0
                + v * a_xi
                + v * v * b_xi
                + v * v * v * c_xi
                + v * v * v * v * s1_xi
                + v * v * v * v * v * s2_xi
                + u * z_xi
                ) `mul` g0

            p1 = pairing (xi `mul` proof1 + (u * xi * omega) `mul` proof2 + f - e) h0
            p2 = pairing (proof1 + u `mul` proof2) h1
