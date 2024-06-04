{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Commitment.KZG where

import           Control.Monad                              (replicateM)
import           Data.ByteString                            (ByteString, empty)
import           Data.Kind                                  (Type)
import           Data.Map.Strict                            (Map, fromList, insert, keys, toList, (!))
import qualified Data.Vector                                as V
import           Data.Vector.Binary                         ()
import           Numeric.Natural                            (Natural)
import           Prelude                                    hiding (Num (..), length, sum, (/), (^))
import qualified Prelude                                    as P
import           Test.QuickCheck                            (Arbitrary (..), chooseInt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Protocol.NonInteractiveProof

-- | `d` is the degree of polynomials in the protocol
newtype KZG c1 c2 t f (d :: Natural) = KZG f
    deriving (Show, Eq, Arbitrary)

newtype WitnessKZG c1 c2 t f d = WitnessKZG { runWitness :: Map f (V.Vector (PolyVec f d)) }
instance (EllipticCurve c1, f ~ ScalarField c1, Show f) => Show (WitnessKZG c1 c2 t f d) where
    show (WitnessKZG w) = "WitnessKZG " <> show w
instance (EllipticCurve c1, f ~ ScalarField c1, KnownNat d, Ring f, Arbitrary f, Ord f) => Arbitrary (WitnessKZG c1 c2 t f d) where
    arbitrary = do
        n <- chooseInt (1, 3)
        m <- chooseInt (1, 5)
        WitnessKZG . fromList <$> replicateM n ((,) <$> arbitrary <*> (V.fromList <$> replicateM m arbitrary))

-- TODO (Issue #18): check list lengths
instance forall (c1 :: Type) (c2 :: Type) t f d kzg .
    ( f ~ ScalarField c1
    , f ~ ScalarField c2
    , Pairing c1 c2 t
    , Binary f
    , KnownNat d
    , KZG c1 c2 t f d ~ kzg
    , P.Num f
    , Ord f
    , Ring f
    , Finite f
    , Field f
    , AdditiveGroup (BaseField c1)
    , Binary (BaseField c1)
    ) => NonInteractiveProof (KZG c1 c2 t f d) where
    type Transcript (KZG c1 c2 t f d)  = ByteString
    type SetupProve (KZG c1 c2 t f d)  = V.Vector (Point c1)
    type SetupVerify (KZG c1 c2 t f d) = (V.Vector (Point c1), Point c2, Point c2)
    type Witness (KZG c1 c2 t f d)     = WitnessKZG c1 c2 t f d
    type Input (KZG c1 c2 t f d)       = ()
    type Proof (KZG c1 c2 t f d)       = (Map f (V.Vector (Point c1), V.Vector f), Map f (Point c1))

    setupProve :: kzg -> SetupProve kzg
    setupProve (KZG x) =
        let d  = value @d
            xs = V.fromList $ map (x^) [0..d-!1]
            gs = fmap (`mul` gen) xs
        in gs
    
    setupVerify :: kzg -> SetupVerify kzg
    setupVerify (KZG x) =
        let d  = value @d
            xs = V.fromList $ map (x^) [0..d-!1]
            gs = fmap (`mul` gen) xs
        in (gs, gen, x `mul` gen)

    prove :: SetupProve kzg
          -> Input kzg
          -> Witness kzg
          -> Proof kzg
    prove gs () (WitnessKZG w) = snd $ foldl proveOne (empty, (mempty, mempty)) (toList w)
        where
            proveOne :: (Transcript kzg, (Map f (V.Vector (Point c1), V.Vector f), Map f (Point c1)))
                     -> (f, V.Vector (PolyVec f d))
                     -> (Transcript kzg, (Map f (V.Vector (Point c1), V.Vector f), Map f (Point c1)))
            proveOne (ts, (iMap, pMap)) (z, fs) = (ts'', (insert z (cms, fzs) iMap, insert z (gs `com` h) pMap))
                where
                    cms  = fmap (com gs) fs
                    fzs  = fmap (`evalPolyVec` z) fs

                    (gamma, ts') = flip challenges (fromIntegral $ V.length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    h            = sum $ V.zipWith scalePV (V.fromList gamma) $ fmap (`provePolyVecEval` z) fs
                    ts''         = if ts == empty then ts' else snd $ challenge @(Transcript kzg) @f ts'

    verify :: SetupVerify kzg -> Input kzg -> Proof kzg -> Bool
    verify (gs, h0, h1) () (input, proof) =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (inf, inf)) $ keys input
                p1 = pairing e0 h0
                p2 = pairing e1 h1
            in p1 == p2
        where
            prepareVerifyOne
                :: (Map f (V.Vector (Point c1), V.Vector f), Map f (Point c1))
                -> (Transcript kzg, (Point c1, Point c1))
                -> f
                -> (Transcript kzg, (Point c1, Point c1))
            prepareVerifyOne (iMap, pMap) (ts, (v0, v1)) z = (ts'', (v0 + v0', v1 + v1'))
                where
                    (cms, fzs) = iMap ! z
                    w          = pMap ! z

                    (gamma', ts') = flip challenges (fromIntegral $ V.length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    gamma = V.fromList gamma'
                    (r, ts'')    = if ts == empty then (one, ts') else challenge ts'

                    v0' = r `mul` sum (V.zipWith mul gamma cms)
                        - r `mul` (gs `com` toPolyVec @f @d [V.sum $ V.zipWith (*) gamma fzs])
                        + (r * z) `mul` w
                    v1' = r `mul` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size f . (KnownNat size, FiniteField f, Eq f) => PolyVec f size -> f -> PolyVec f size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) `polyVecDiv` toPolyVec [negate z, one]

com :: (EllipticCurve curve, f ~ ScalarField curve) => V.Vector (Point curve) -> PolyVec f size -> Point curve
com gs f = sum $ V.zipWith mul (fromPolyVec f) gs
