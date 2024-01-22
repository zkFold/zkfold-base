{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.Commitment.KZG where

import           Data.ByteString                             (ByteString, empty)
import           Data.Map                                    (Map, (!), insert, toList, keys, fromList)
import           Data.Data                                   (Typeable)
import           Prelude                                     hiding (Num(..), (^), (/), sum, length)
import           Test.QuickCheck                             (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                              (length)

-- TODO (Issue #24): make this module generic in the elliptic curve with pairing

type F = ScalarField BLS12_381_G1
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

type PolyVecEvalInput size = (PolyVec F size, F)
type PolyVecEvalProof size = (F, PolyVec F size)

data KZG d

-- TODO (Issue #24): move this to another module
data D32
instance Finite D32 where
    order = 32

-- The degree of polynomials in the protocol
instance Finite d => Finite (KZG d) where
    order = order @d

newtype WitnessKZG d = WitnessKZG (Map F [PolyVec F (KZG d)])
    deriving Show
instance Finite d => Arbitrary (WitnessKZG d) where
    arbitrary = do
        n <- chooseInteger (1, 3)
        m <- chooseInteger (1, 5)
        WitnessKZG . fromList <$> mapM (const $ (,) <$> arbitrary <*> mapM (const arbitrary) [1..m]) [1..n]

-- TODO (Issue #18): check list lengths
instance forall d . (Finite d, Typeable (KZG d)) => NonInteractiveProof (KZG d) where
    type Transcript (KZG d)   = ByteString
    type Params (KZG d)       = ()
    type SetupSecret (KZG d)  = F
    type Setup (KZG d)        = ([G1], G2, G2)
    type ProverSecret (KZG d) = ()
    type Witness (KZG d)      = Map F [PolyVec F (KZG d)]
    type Input (KZG d)        = Map F ([G1], [F])
    type Proof (KZG d)        = Map F G1

    setup :: Params (KZG d) -> SetupSecret (KZG d) -> Setup (KZG d)
    setup _ x =
        let d  = order @(KZG d)
            xs = map (x^) [0..d-1]
            gs = map (`mul` gen) xs
        in (gs, gen, x `mul` gen)

    prove :: ProverSecret (KZG d) -> Setup (KZG d) -> Witness (KZG d) -> (Input (KZG d), Proof (KZG d))
    prove _ (gs, _, _) w = snd $ foldl proveOne (empty, (mempty, mempty)) (toList w)
        where
            proveOne :: (Transcript (KZG d), (Input (KZG d), Proof (KZG d)))
                -> (F, [PolyVec F (KZG d)])
                -> (Transcript (KZG d), (Input (KZG d), Proof (KZG d)))
            proveOne (ts, (iMap, pMap)) (z, fs) = (ts'', (insert z (cms, fzs) iMap, insert z (gs `com` h) pMap))
                where
                    cms  = map (com gs) fs
                    fzs  = map (`evalPolyVec` z) fs

                    (gamma, ts') = flip challenges (length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    h            = sum $ zipWith scalePV gamma  $ map (`provePolyVecEval` z) fs
                    ts''         = if ts == empty then ts' else snd $ challenge @(Transcript (KZG d)) @F ts'

    verify :: Setup (KZG d) -> Input (KZG d) -> Proof (KZG d) -> Bool
    verify (gs, h0, h1) input proof =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (inf, inf)) $ keys input
                p1 = pairing e0 h0
                p2 = pairing e1 h1
            in p1 == p2
        where
            prepareVerifyOne :: (Input (KZG d), Proof (KZG d)) -> (Transcript (KZG d), (G1, G1)) -> F -> (Transcript (KZG d), (G1, G1))
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
                        - r `mul` (gs `com` toPolyVec @F @(KZG d) [sum $ zipWith (*) gamma fzs])
                        + (r * z) `mul` w
                    v1' = r `mul` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size . Finite size => PolyVec F size -> F -> PolyVec F size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) / toPolyVec [negate z, one]

com :: [G1] -> PolyVec F size -> G1
com gs f = sum $ zipWith mul (fromPolyVec f) gs