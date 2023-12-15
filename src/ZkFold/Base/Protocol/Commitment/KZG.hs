{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.Commitment.KZG where

import           Data.ByteString                             (empty)
import           Data.Map                                    (Map, (!), insert, toList, keys)
import           Prelude                                     hiding (Num(..), (^), (/), sum, length)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                              (length)

-- TODO: make this module generic in the elliptic curve with pairing

type F = ScalarField BLS12_381_G1
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

type PolyVecEvalInput size = (PolyVec F size, F)
type PolyVecEvalProof size = (F, PolyVec F size)

data KZG

-- The degree of polynomials in the protocol
-- TODO: remove hard-coding
instance Finite KZG where
    order = 32

-- TODO: check list lengths
instance NonInteractiveProof KZG where
    type Params KZG       = ()
    type SetupSecret KZG  = F
    type Setup KZG        = ([G1], G2, G2)
    type ProverSecret KZG = ()
    type Witness KZG      = Map F [PolyVec F KZG]
    type Input KZG        = Map F ([G1], [F])
    type Proof KZG        = Map F G1

    setup :: Params KZG -> SetupSecret KZG -> Setup KZG
    setup _ x =
        let d  = order @KZG
            xs = map (x^) [0..d-1]
            gs = map (`mul` gen) xs
        in (gs, gen, x `mul` gen)

    prove :: ProverSecret KZG -> Setup KZG -> Witness KZG -> (Input KZG, Proof KZG)
    prove _ (gs, _, _) w = snd $ foldl proveOne (empty, (mempty, mempty)) (toList w)
        where
            proveOne :: (Transcript, (Input KZG, Proof KZG))
                -> (F, [PolyVec F KZG])
                -> (Transcript, (Input KZG, Proof KZG))
            proveOne (ts, (iMap, pMap)) (z, fs) = (ts'', (insert z (cms, fzs) iMap, insert z (gs `com` h) pMap))
                where
                    cms  = map (com gs) fs
                    fzs  = map (`evalPolyVec` z) fs

                    (gamma, ts') = flip challenges (length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    h            = sum $ zipWith scalePV gamma  $ map (`provePolyVecEval` z) fs
                    ts''         = if ts == empty then ts' else snd $ challenge @F ts'

    verify :: Setup KZG -> Input KZG -> Proof KZG -> Bool
    verify (gs, h0, h1) input proof =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (inf, inf)) $ keys input
                p1 = pairing e0 h0
                p2 = pairing e1 h1
            in p1 == p2
        where
            prepareVerifyOne :: (Input KZG, Proof KZG) -> (Transcript, (G1, G1)) -> F -> (Transcript, (G1, G1))
            prepareVerifyOne (iMap, pMap) (ts, (v0, v1)) z = (ts'', (v0 + v0', v1 + v1'))
                where
                    (cms, fzs) = iMap ! z
                    w          = pMap ! z

                    (gamma, ts') = flip challenges (length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    (r, ts'')    = if ts == empty then (one, ts') else challenge ts'

                    v0' = r `mul` sum (zipWith mul gamma cms)
                        - r `mul` (gs `com` toPolyVec @F @KZG [sum $ zipWith (*) gamma fzs])
                        + (r * z) `mul` w
                    v1' = r `mul` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size . Finite size => PolyVec F size -> F -> PolyVec F size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) / toPolyVec [negate z, one]

com :: [G1] -> PolyVec F size -> G1
com gs f = sum $ zipWith mul (fromPolyVec f) gs