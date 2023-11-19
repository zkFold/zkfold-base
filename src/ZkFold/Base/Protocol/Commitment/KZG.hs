{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.Commitment.KZG where

import           Data.ByteString                             (empty)
import           Prelude                                     hiding (Num(..), (^), (/), sum, negate, replicate, length, splitAt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                              (length)

-- TODO: generalize this to arbitrary number of evaluation points

type F = ScalarField BLS12_381_G1
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

type PolyVecEvalInput size = (PolyVec F size, F)
type PolyVecEvalProof size = (F, PolyVec F size)

data WitnessKZG size = WitnessKZG F [PolyVec F size] F [PolyVec F size]
data InputKZG = InputKZG F [G1] [F] F [G1] [F]
data ProofKZG = ProofKZG G1 G1

data KZG

-- The degree of polynomials in the protocol
-- TODO: remove hard-coding
instance Finite KZG where
    order = 32

-- TODO: check list lengths
instance NonInteractiveProof KZG where
    type Params KZG       = Integer
    type SetupSecret KZG  = F
    type Setup KZG        = ([G1], G2, G2)
    type ProverSecret KZG = ()
    type Witness KZG      = WitnessKZG KZG
    type Input KZG        = InputKZG
    type Proof KZG        = ProofKZG

    setup :: Params KZG -> SetupSecret KZG -> Setup KZG
    setup d x =
        let xs = map (x^) [0..d-1]
            gs = map (`mul` gen) xs
        in (gs, gen, x `mul` gen)

    prove :: ProverSecret KZG -> Setup KZG -> Witness KZG -> (Input KZG, Proof KZG)
    prove _ (gs, _, _) (WitnessKZG z fs z' fs') =
        let cms  = map (com gs) fs
            cms' = map (com gs) fs'

            fzs  = map (fst . (`provePolyVecEval` z)) fs
            fzs' = map (fst . (`provePolyVecEval` z')) fs'

            ts = empty
                `transcript` z
                `transcript` z'
                `transcript` fzs
                `transcript` fzs'
                `transcript` cms
                `transcript` cms'
            (gamma, ts') = challenges ts  (length cms)
            (gamma', _)  = challenges ts' (length cms')

            h    = sum $ zipWith scalePV gamma  $ map (snd . (`provePolyVecEval` z)) fs
            h'   = sum $ zipWith scalePV gamma' $ map (snd . (`provePolyVecEval` z)) fs
        in (InputKZG z cms fzs z' cms' fzs', ProofKZG (gs `com` h) (gs `com` h'))

    verify :: Setup KZG -> Input KZG -> Proof KZG -> Bool
    verify (gs, h0, h1) (InputKZG z cms fzs z' cms' fzs') (ProofKZG w w') =
        let ts = empty
                `transcript` z
                `transcript` z'
                `transcript` fzs
                `transcript` fzs'
                `transcript` cms
                `transcript` cms'
            (gamma, ts')   = challenges ts  (length cms)
            (gamma', ts'') = challenges ts' (length cms')
            (r, _)         = challenge ts''

            v = sum (zipWith mul gamma cms)
                - gs `com` toPolyVec @F @KZG [sum $ zipWith (*) gamma fzs]
                + r `mul` sum (zipWith mul gamma' cms')
                - r `mul` (gs `com` toPolyVec @F @KZG [sum $ zipWith (*) gamma' fzs'])

            p1 = pairing (v + z `mul` w + (r*z') `mul` w') h0
            p2 = pairing (w + r `mul` w') h1
        in p1 == p2

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size . Finite size => PolyVec F size -> F -> PolyVecEvalProof size
provePolyVecEval f z =
    let zs = map (z^) [0 .. order @size - 1]
        fz = sum $ zipWith (*) (fromPolyVec f) zs
    in (fz, (f - toPolyVec [negate fz]) / toPolyVec [z, one])

com :: [G1] -> PolyVec F size -> G1
com gs f = sum $ zipWith mul (fromPolyVec f) gs