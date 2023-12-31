{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.ARK.Plonk where

import           Data.ByteString                             (ByteString)
import           Data.Data                                   (Typeable)
import           Data.Map                                    (Map, singleton, elems)
import qualified Data.Map                                    as Map
import           Prelude                                     hiding (Num(..), (^), (/), (!!), sum, length, take, drop, replicate)
import           Test.QuickCheck                             (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp, fromZp)
import           ZkFold.Base.Algebra.Basic.Permutations      (Permutation(..), fromCycles, mkIndexPartition)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate  hiding (qr)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (toPlonkArithmetization, getParams)
import           ZkFold.Base.Protocol.Commitment.KZG         (com)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                              (take, drop, (!))
import           ZkFold.Symbolic.Arithmetization             (ArithmeticCircuit (..), mapVarArithmeticCircuit)

-- TODO: make this module generic in the elliptic curve with pairing

type F = Zp BLS12_381_Scalar
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

data Plonk t

type PlonkBS = Plonk ByteString

-- TODO: We should have several options for size of the polynomials. Most code should be generic in this parameter.
instance Finite (Plonk t) where
    -- n
    order = 32

-- TODO: check that the extended polynomials are of the right size
data PlonkMaxPolyDegree t
type PlonkMaxPolyDegreeBS = PlonkMaxPolyDegree ByteString
instance Finite (PlonkMaxPolyDegree t) where
    -- 4n + 7
    order = 4 * order @(Plonk t) + 7
type PolyPlonkExtended t = PolyVec F (PlonkMaxPolyDegree t)

data ParamsPlonk = ParamsPlonk F F F (Map Integer F) (ArithmeticCircuit F)
    deriving (Show)
-- TODO: make a proper implementation of Arbitrary
instance Arbitrary ParamsPlonk where
    arbitrary = do
        let (omega, k1, k2) = getParams 5
        ac <- arbitrary
        return $ ParamsPlonk omega k1 k2 (singleton (acOutput ac) 15) ac

data ProverSecretPlonk = ProverSecretPlonk F F F F F F F F F F F
    deriving (Show)
instance Arbitrary ProverSecretPlonk where
    arbitrary = ProverSecretPlonk <$>
        arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

newtype WitnessMapPlonk t = WitnessMap (Map.Map Integer F -> (PolyVec F (Plonk t), PolyVec F (Plonk t), PolyVec F (Plonk t)))
-- TODO: make a proper implementation of Show
instance Show (WitnessMapPlonk t) where
    show _ = "WitnessMap"

newtype WitnessInputPlonk = WitnessInputPlonk (Map.Map Integer F)
-- TODO: make a proper implementation of Show
instance Show WitnessInputPlonk where
    show _ = "WitnessInput"
-- TODO: make a proper implementation of Arbitrary
instance Arbitrary WitnessInputPlonk where
    arbitrary = do
        x <- arbitrary
        return $ WitnessInputPlonk $ Map.fromList [(1, x), (2, 15/x)]

-- TODO: check list lengths
instance forall t . (Typeable t, ToTranscript t F, ToTranscript t G1, FromTranscript t F) => NonInteractiveProof (Plonk t) where
    type Transcript (Plonk t)   = t
    type Params (Plonk t)       = ParamsPlonk
    type SetupSecret (Plonk t)  = F
    type Setup (Plonk t)        = (([F], [G1], G2, G2, F, F, F),
        (PolyPlonkExtended t, PolyPlonkExtended t, PolyPlonkExtended t, PolyPlonkExtended t, PolyPlonkExtended t,
        PolyPlonkExtended t, PolyPlonkExtended t, PolyPlonkExtended t),
        (G1, G1, G1, G1, G1,
        G1, G1, G1),
        WitnessMapPlonk t, (PolyVec F (Plonk t), PolyVec F (Plonk t), PolyVec F (Plonk t)))
    type ProverSecret (Plonk t) = ProverSecretPlonk
    type Witness (Plonk t)      = WitnessInputPlonk
    type Input (Plonk t)        = [F]
    type Proof (Plonk t)        = (G1, G1, G1, G1, G1, G1, G1, G1, G1, F, F, F, F, F, F)

    setup :: Params (Plonk t) -> SetupSecret (Plonk t) -> Setup (Plonk t)
    setup (ParamsPlonk omega k1 k2 inputs ac) x =
        let wmap = acWitness $ mapVarArithmeticCircuit ac
            (ql, qr, qo, qm, qc, a, b, c) = toPlonkArithmetization inputs ac
            wPub = map negate $ elems inputs

            d = order @(Plonk t) + 6
            xs = map (x^) [0..d-1]
            gs = map (`mul` gen) xs
            h0 = gen
            h1 = x `mul` gen

            Permutation s = fromCycles $ mkIndexPartition $ map fromZp $ fromPolyVec a ++ fromPolyVec b ++ fromPolyVec c
            f i = case (i-1) `div` order @(Plonk t) of
                0 -> omega^i
                1 -> k1 * (omega^i)
                2 -> k2 * (omega^i)
                _ -> error "setup: invalid index"
            s' = map f s
            sigma1 = toPolyVec $ take (order @(Plonk t)) s'
            sigma2 = toPolyVec $ take (order @(Plonk t)) $ drop (order @(Plonk t)) s'
            sigma3 = toPolyVec $ take (order @(Plonk t)) $ drop (2 * order @(Plonk t)) s'
            w1 i    = toPolyVec $ map ((wmap i !) . fromZp) (fromPolyVec a)
            w2 i    = toPolyVec $ map ((wmap i !) . fromZp) (fromPolyVec b)
            w3 i    = toPolyVec $ map ((wmap i !) . fromZp) (fromPolyVec c)
            wmap' i = (w1 i, w2 i, w3 i)

            qmE     = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega qm
            qlE     = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega ql
            qrE     = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega qr
            qoE     = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega qo
            qcE     = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega qc
            sigma1E = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega sigma1
            sigma2E = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega sigma2
            sigma3E = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega sigma3
        in ((wPub, gs, h0, h1, omega, k1, k2), (qlE, qrE, qoE, qmE, qcE, sigma1E, sigma2E, sigma3E),
            (gs `com` qlE, gs `com` qrE, gs `com` qoE, gs `com` qmE, gs `com` qcE,
            gs `com` sigma1E, gs `com` sigma2E, gs `com` sigma3E), WitnessMap wmap', (sigma1, sigma2, sigma3))

    prove :: ProverSecret (Plonk t) -> Setup (Plonk t) -> Witness (Plonk t) -> (Input (Plonk t), Proof (Plonk t))
    prove
        (ProverSecretPlonk b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11)
        ((wPub, gs, _, _, omega, k1, k2), (ql, qr, qo, qm, qc, sigma1, sigma2, sigma3), _, WitnessMap wmap, (sigma1s, sigma2s, sigma3s))
        (WitnessInputPlonk wInput) = (wPub, (cmA, cmB, cmC, cmZ, cmT1, cmT2, cmT3, proof1, proof2, a_xi, b_xi, c_xi, s1_xi, s2_xi, z_xi))
        where
            n = order @(Plonk t)
            zH = polyVecZero @F @(Plonk t) @(PlonkMaxPolyDegree t)

            (w1, w2, w3) = wmap wInput
            pubPoly = polyVecInLagrangeBasis omega $ toPolyVec @F @(Plonk t) wPub

            a = polyVecLinear b2 b1 * zH + polyVecInLagrangeBasis omega w1
            b = polyVecLinear b4 b3 * zH + polyVecInLagrangeBasis omega w2
            c = polyVecLinear b6 b5 * zH + polyVecInLagrangeBasis omega w3

            cmA = gs `com` a
            cmB = gs `com` b
            cmC = gs `com` c

            (beta, ts) = challenge $ mempty
                `transcript` cmA
                `transcript` cmB
                `transcript` cmC
            (gamma, ts') = challenge ts

            omegas  = toPolyVec $ map (omega ^) [1 .. n]
            omegas' =  map (omega ^) [0 :: Integer .. ]
            PV zs1 = polyVecGrandProduct w1 omegas sigma1s beta gamma
            PV zs2 = polyVecGrandProduct w2 (scalePV k1 omegas) sigma2s beta gamma
            PV zs3 = polyVecGrandProduct w3 (scalePV k2 omegas) sigma3s beta gamma
            gp = PV $ zipWith (*) (zipWith (*) zs1 zs2) zs3
            z  = polyVecQuadratic b9 b8 b7 * zH + polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega gp
            zo = toPolyVec $ zipWith (*) (fromPolyVec z) omegas'
            cmZ = gs `com` z

            (alpha, ts'') = challenge $ ts' `transcript` cmZ :: (F, Transcript (Plonk t))

            t1  = a * b * qm + a * ql + b * qr + c * qo + pubPoly + qc
            t2  = (a + polyVecLinear gamma beta)
                * (b + polyVecLinear gamma (beta * k1))
                * (c + polyVecLinear gamma (beta * k2))
                * z
            t3  = (a + scalePV beta sigma1 + scalePV gamma one)
                * (b + scalePV beta sigma2 + scalePV gamma one)
                * (c + scalePV beta sigma3 + scalePV gamma one)
                * zo
            t4 = (z - one) * polyVecLagrange @F @(Plonk t) @(PlonkMaxPolyDegree t) 1 omega
            t = (t1 + scalePV alpha (t2 - t3) + scalePV (alpha * alpha) t4) / zH

            t_lo'  = toPolyVec $ take n $ fromPolyVec t
            t_mid' = toPolyVec $ take n $ drop n $ fromPolyVec t
            t_hi'  = toPolyVec $ drop (2*n) $ fromPolyVec t
            t_lo   = t_lo' + scalePV b10 (polyVecZero @F @(Plonk t) @(PlonkMaxPolyDegree t) + one)
            t_mid  = t_mid' + scalePV b11 (polyVecZero @F @(Plonk t) @(PlonkMaxPolyDegree t) + one) - scalePV b10 one
            t_hi   = t_hi' - scalePV b11 one
            cmT1   = gs `com` t_lo
            cmT2   = gs `com` t_mid
            cmT3   = gs `com` t_hi

            (xi, ts''') = challenge $ ts''
                `transcript` cmT1
                `transcript` cmT2
                `transcript` cmT3

            a_xi  = evalPolyVec a xi
            b_xi  = evalPolyVec b xi
            c_xi  = evalPolyVec c xi
            s1_xi = evalPolyVec sigma1 xi
            s2_xi = evalPolyVec sigma2 xi
            z_xi  = evalPolyVec z (xi * omega)

            (v, _) = challenge $ ts'''
                `transcript` a_xi
                `transcript` b_xi
                `transcript` c_xi
                `transcript` s1_xi
                `transcript` s2_xi
                `transcript` z_xi

            lagrange1_xi = polyVecLagrange @F @(Plonk t) @(PlonkMaxPolyDegree t) 1 omega `evalPolyVec` xi
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
                ) / polyVecLinear (negate xi) one
            proof2Poly = (z - scalePV z_xi one) / toPolyVec [negate (xi * omega), one]
            proof1 = gs `com` proof1Poly
            proof2 = gs `com` proof2Poly

    verify :: Setup (Plonk t) -> Input (Plonk t) -> Proof (Plonk t) -> Bool
    verify
        ((_, gs, h0, h1, omega, k1, k2), _, (cmQl, cmQr, cmQo, cmQm, cmQc, cmS1, cmS2, cmS3), _, _)
        ws
        (cmA, cmB, cmC, cmZ, cmT1, cmT2, cmT3, proof1, proof2, a_xi, b_xi, c_xi, s1_xi, s2_xi, z_xi) = p1 == p2
        where
            n = order @(Plonk t)

            (beta, ts) = challenge $ mempty
                `transcript` cmA
                `transcript` cmB
                `transcript` cmC :: (F, Transcript (Plonk t))
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

            zH_xi        = polyVecZero @F @(Plonk t) @(PlonkMaxPolyDegree t) `evalPolyVec` xi
            lagrange1_xi = polyVecLagrange @F @(Plonk t) @(PlonkMaxPolyDegree t) 1 omega `evalPolyVec` xi
            pubPoly_xi   = polyVecInLagrangeBasis @F @(Plonk t) @(PlonkMaxPolyDegree t) omega (toPolyVec ws) `evalPolyVec` xi

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
                ) `mul` head gs

            p1 = pairing (xi `mul` proof1 + (u * xi * omega) `mul` proof2 + f - e) h0
            p2 = pairing (proof1 + u `mul` proof2) h1