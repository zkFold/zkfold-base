{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Base.Protocol.Commitment.KZG where

import           Control.Monad                              (replicateM)
import           Data.ByteString                            (ByteString, empty)
import           Data.Kind                                  (Type)
import           Data.Map.Strict                            (Map, fromList, insert, keys, toList, (!))
import           Prelude                                    hiding (Num (..), length, sum, (/), (^))
import           Test.QuickCheck                            (Arbitrary (..), chooseInt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString                (FromByteString, ToByteString)
import           ZkFold.Base.Protocol.NonInteractiveProof
import           ZkFold.Prelude                             (length)

newtype KZG c1 c2 t f d = KZG f
    deriving (Show, Eq, Arbitrary)

-- The degree of polynomials in the protocol
instance Finite d => Finite (KZG c1 c2 t f d) where
    order = order @d

newtype WitnessKZG c1 c2 t f d = WitnessKZG { runWitness :: Map f [PolyVec f (KZG c1 c2 t f d)] }
instance (EllipticCurve c1, f ~ ScalarField c1) => Show (WitnessKZG c1 c2 t f d) where
    show (WitnessKZG w) = "WitnessKZG " <> show w
instance (EllipticCurve c1, f ~ ScalarField c1, Finite d) => Arbitrary (WitnessKZG c1 c2 t f d) where
    arbitrary = do
        n <- chooseInt (1, 3)
        m <- chooseInt (1, 5)
        WitnessKZG . fromList <$> replicateM n ((,) <$> arbitrary <*> replicateM m arbitrary)

-- TODO (Issue #18): check list lengths
instance forall (c1 :: Type) (c2 :: Type) t f d kzg . (f ~ ScalarField c1, f ~ ScalarField c2,
        Pairing c1 c2 t, ToByteString f, FromByteString f, Finite d, KZG c1 c2 t f d ~ kzg)
        => NonInteractiveProof (KZG c1 c2 t f d) where
    type Transcript (KZG c1 c2 t f d)   = ByteString
    type Setup (KZG c1 c2 t f d)        = ([Point c1], Point c2, Point c2)
    type Witness (KZG c1 c2 t f d)      = WitnessKZG c1 c2 t f d
    type Input (KZG c1 c2 t f d)        = Map f ([Point c1], [f])
    type Proof (KZG c1 c2 t f d)        = Map f (Point c1)

    setup :: kzg -> Setup kzg
    setup (KZG x) =
        let d  = order @kzg
            xs = map (x^) [0..d-1]
            gs = map (`mul` gen) xs
        in (gs, gen, x `mul` gen)

    prove :: Setup kzg
          -> Witness kzg
          -> (Input kzg, Proof kzg)
    prove (gs, _, _) (WitnessKZG w) = snd $ foldl proveOne (empty, (mempty, mempty)) (toList w)
        where
            proveOne :: (Transcript kzg, (Input kzg, Proof kzg))
                     -> (f, [PolyVec f kzg])
                     -> (Transcript kzg, (Input kzg, Proof kzg))
            proveOne (ts, (iMap, pMap)) (z, fs) = (ts'', (insert z (cms, fzs) iMap, insert z (gs `com` h) pMap))
                where
                    cms  = map (com gs) fs
                    fzs  = map (`evalPolyVec` z) fs

                    (gamma, ts') = flip challenges (length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    h            = sum $ zipWith scalePV gamma  $ map (`provePolyVecEval` z) fs
                    ts''         = if ts == empty then ts' else snd $ challenge @(Transcript kzg) @f ts'

    verify :: Setup kzg -> Input kzg -> Proof kzg -> Bool
    verify (gs, h0, h1) input proof =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (inf, inf)) $ keys input
                p1 = pairing e0 h0
                p2 = pairing e1 h1
            in p1 == p2
        where
            prepareVerifyOne :: (Input kzg, Proof kzg)
                             -> (Transcript kzg, (Point c1, Point c1))
                             -> f
                             -> (Transcript kzg, (Point c1, Point c1))
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
                        - r `mul` (gs `com` toPolyVec @f @kzg [sum $ zipWith (*) gamma fzs])
                        + (r * z) `mul` w
                    v1' = r `mul` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size f . (Finite size, FiniteField f, Eq f) => PolyVec f size -> f -> PolyVec f size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) / toPolyVec [negate z, one]

com :: (EllipticCurve curve, f ~ ScalarField curve) => [Point curve] -> PolyVec f size -> Point curve
com gs f = sum $ zipWith mul (fromPolyVec f) gs
