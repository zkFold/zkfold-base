{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.ARK.Plonk where

import           Data.ByteString                             (empty)
import           Prelude                                     hiding (Num(..), (^), (/), (!!), sum, length, take, drop)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate  hiding (qr)
import           ZkFold.Base.Protocol.Commitment.KZG
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                              (take, drop)

data Plonk

instance Finite Plonk where
    -- n
    order = order @KZG - 6

data PlonkMaxPolyDegree
instance Finite PlonkMaxPolyDegree where
    -- 4n + 5
    order = 4 * order @Plonk + 5
type PolyPlonkExtended = PolyVec F PlonkMaxPolyDegree

-- TODO: check list lengths
instance NonInteractiveProof Plonk where
    type Params Plonk       = (Integer, F, F, F,
        PolyVec F Plonk, PolyVec F Plonk, PolyVec F Plonk, PolyVec F Plonk, PolyVec F Plonk,
        PolyVec F Plonk, PolyVec F Plonk, PolyVec F Plonk)
    type SetupSecret Plonk  = F
    type Setup Plonk        = (Integer, [G1], G2, G2, F, F, F,
        PolyPlonkExtended, PolyPlonkExtended, PolyPlonkExtended, PolyPlonkExtended, PolyPlonkExtended,
        PolyPlonkExtended, PolyPlonkExtended, PolyPlonkExtended,
        G1, G1, G1, G1, G1,
        G1, G1, G1)
    type ProverSecret Plonk = (F, F, F, F, F, F, F, F, F, F, F)
    type Witness Plonk      = (PolyVec F Plonk, PolyVec F Plonk, PolyVec F Plonk)
    type Input Plonk        = [F]
    type Proof Plonk        = (G1, G1, G1, G1, G1, G1, G1, G1, G1, F, F, F, F, F, F)

    setup :: Params Plonk -> SetupSecret Plonk -> Setup Plonk
    setup (l, omega, k1, k2, qm, ql, qr, qo, qc, sigma1, sigma2, sigma3) x =
        let (gs, h0, h1) = setup @KZG () x
            qmE     = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega qm
            qlE     = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega ql
            qrE     = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega qr
            qoE     = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega qo
            qcE     = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega qc
            sigma1E = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega sigma1
            sigma2E = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega sigma2
            sigma3E = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree (order @Plonk) omega sigma3
        in (l, gs, h0, h1, omega, k1, k2, qmE, qlE, qrE, qoE, qcE, sigma1E, sigma2E, sigma3E,
            gs `com` qmE, gs `com` qlE, gs `com` qrE, gs `com` qoE, gs `com` qcE,
            gs `com` sigma1E, gs `com` sigma2E, gs `com` sigma3E)

    prove :: ProverSecret Plonk -> Setup Plonk -> Witness Plonk -> (Input Plonk, Proof Plonk)
    prove
        (b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11)
        (l, gs, _, _, omega, k1, k2, qm, ql, qr, qo, qc, sigma1, sigma2, sigma3, _, _, _, _, _, _, _, _)
        (w1, w2, w3) = (ws, (cmA, cmB, cmC, cmZ, cmT1, cmT2, cmT3, proof1, proof2, a_xi, b_xi, c_xi, s1_xi, s2_xi, z_xi))
        where
            n = order @Plonk
            zH = polyVecZero n
            ws  = take l $ fromPolyVec w1
            pubPoly = polyVecInLagrangeBasis n omega $ toPolyVec @F @PlonkMaxPolyDegree ws

            a = polyVecLinear b2 b1 * zH + castPolyVec @F @Plonk @PlonkMaxPolyDegree (polyVecInLagrangeBasis n omega w1)
            b = polyVecLinear b4 b3 * zH + castPolyVec @F @Plonk @PlonkMaxPolyDegree (polyVecInLagrangeBasis n omega w2)
            c = polyVecLinear b6 b5 * zH + castPolyVec @F @Plonk @PlonkMaxPolyDegree (polyVecInLagrangeBasis n omega w3)

            cmA = gs `com` a
            cmB = gs `com` b
            cmC = gs `com` c

            (beta, ts) = challenge $ empty
                `transcript` cmA
                `transcript` cmB
                `transcript` cmC
            (gamma, ts') = challenge ts

            omegas = map (omega ^) [0..n-1]
            sigmas1 = omegas
            sigmas2 = map (*k1) omegas
            sigmas3 = map (*k2) omegas
            PV zs1 = polyVecGrandProduct w1 (PV omegas) (PV sigmas1) beta gamma
            PV zs2 = polyVecGrandProduct w2 (PV omegas) (PV sigmas2) beta gamma
            PV zs3 = polyVecGrandProduct w3 (PV omegas) (PV sigmas3) beta gamma
            gp = PV $ one : tail (zipWith (*) (zipWith (*) zs1 zs2) zs3)
            z  = polyVecQuadratic b9 b8 b7 * zH + polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree n omega gp
            zo = toPolyVec $ zipWith (*) (fromPolyVec z) (omegas ++ [omega^n, omega^(n+1), omega^(n+2)])
            cmZ = gs `com` z

            (alpha, ts'') = challenge $ ts' `transcript` cmZ :: (F, Transcript)

            t = (a * b * qm + a * ql + b * qr + c * qo + pubPoly + qc) / zH
                + scalePV alpha (a + polyVecLinear gamma beta) * (b + polyVecLinear gamma (beta * k1)) * (c + polyVecLinear gamma (beta * k2)) * z / zH
                - scalePV alpha (a + scalePV beta sigma1 + scalePV gamma one) * (b + scalePV beta sigma2 + scalePV gamma one) * (c + scalePV beta sigma3 + scalePV gamma one) * zo / zH
                + scalePV (alpha * alpha) (z - one) * polyVecLagrange n 1 omega
            t_lo'  = PV $ take n $ fromPolyVec t
            t_mid' = PV $ take n $ drop n $ fromPolyVec t
            t_hi'  = PV $ drop (2*n) $ fromPolyVec t
            t_lo   = t_lo' + scalePV b10 (polyVecZero n)
            t_mid  = t_mid' + scalePV b11 (polyVecZero n) - scalePV b10 one
            t_hi   = t_hi' - scalePV b11 one
            cmT1   = gs `com` t_lo
            cmT2   = gs `com` t_mid
            cmT3   = gs `com` t_hi

            (xi, ts''') = challenge $ ts''
                `transcript` cmT1
                `transcript` cmT2
                `transcript` cmT3

            a_xi = evalPolyVec a xi
            b_xi = evalPolyVec b xi
            c_xi = evalPolyVec c xi
            s1_xi = evalPolyVec sigma1 xi
            s2_xi = evalPolyVec sigma2 xi
            z_xi = evalPolyVec z (xi * omega)

            (v, _) = challenge $ ts'''
                `transcript` a_xi
                `transcript` b_xi
                `transcript` c_xi
                `transcript` s1_xi
                `transcript` s2_xi
                `transcript` z_xi

            lagrange1_xi = polyVecLagrange @F @PlonkMaxPolyDegree n 1 omega `evalPolyVec` xi
            zH_xi = zH `evalPolyVec` xi
            r = scalePV (a_xi * b_xi) qm + scalePV a_xi ql + scalePV b_xi qr + scalePV c_xi qo + scalePV (pubPoly `evalPolyVec` xi) one + qc
                + scalePV alpha (scalePV ((a_xi + beta * xi + gamma) * (b_xi + beta * k1 * xi + gamma) * (c_xi + beta * k2 * xi + gamma)) z
                    - scalePV ((a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * z_xi) (scalePV beta sigma3 + scalePV (c_xi + gamma) one))
                + scalePV (alpha * alpha * lagrange1_xi) (z - one)
                - scalePV zH_xi (scalePV (xi^ (2 *n)) t_hi + scalePV (xi^n) t_mid + t_lo)

            proof1Poly = (r + scalePV v (a - scale a_xi one) + scalePV (v * v) (b - scale b_xi one) + scalePV (v * v * v) (c - scale c_xi one)
                + scalePV (v * v * v * v) (sigma1 - scale s1_xi one) + scalePV (v * v * v * v * v) (sigma2 - scale s2_xi one)) / polyVecLinear (negate xi) one
            proof2Poly = (z - scale z_xi one) / polyVecLinear (negate xi * omega) one
            proof1 = gs `com` proof1Poly
            proof2 = gs `com` proof2Poly

    verify :: Setup Plonk -> Input Plonk -> Proof Plonk -> Bool
    verify
        (_, gs, h0, h1, omega, k1, k2, _, _, _, _, _, _, _, _, cmQm, cmQl, cmQr, cmQo, cmQc, cmS1, cmS2, cmS3)
        ws
        (cmA, cmB, cmC, cmZ, cmT1, cmT2, cmT3, proof1, proof2, a_xi, b_xi, c_xi, s1_xi, s2_xi, z_xi) = p1 == p2
        where
            n = order @Plonk

            (beta, ts) = challenge $ empty
                `transcript` cmA
                `transcript` cmB
                `transcript` cmC :: (F, Transcript)
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

            zH_xi        = polyVecZero @F @PlonkMaxPolyDegree n `evalPolyVec` xi
            lagrange1_xi = polyVecLagrange @F @PlonkMaxPolyDegree n 1 omega `evalPolyVec` xi
            pubPoly_xi   = polyVecInLagrangeBasis @F @Plonk @PlonkMaxPolyDegree n omega (toPolyVec ws) `evalPolyVec` xi

            r0 = pubPoly_xi - lagrange1_xi * alpha * alpha - alpha * (a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * (c_xi + gamma) * z_xi
            d  = scale (a_xi * b_xi) cmQm + scale a_xi cmQl + scale b_xi cmQr + scale c_xi cmQo + cmQc
                + scale ((a_xi + beta * xi + gamma) * (b_xi + beta * k1 * xi + gamma) * (c_xi + beta * k2 * xi + gamma) * alpha + lagrange1_xi * alpha * alpha + u) cmZ
                - scale ((a_xi + beta * s1_xi + gamma) * (b_xi + beta * s2_xi + gamma) * alpha * beta * z_xi) cmS3
                - scale zH_xi (cmT1 + xi^n `scale` cmT2 + xi^(2*n) `scale` cmT3)
            f  = d + v `scale` cmA + (v * v) `scale` cmB + (v * v * v) `scale` cmC + (v * v * v * v) `scale` cmS1 + (v * v * v * v * v) `scale` cmS2
            e  = (-r0 + v * a_xi + v * v * b_xi + v * v * v * c_xi + v * v * v * v * s1_xi + v * v * v * v * v * s2_xi + u * z_xi) `scale` head gs

            p1 = pairing (xi `mul` proof1 + (u * xi * omega) `mul` proof2 + f - e) h0
            p2 = pairing (proof1 + u `scale` proof2) h1