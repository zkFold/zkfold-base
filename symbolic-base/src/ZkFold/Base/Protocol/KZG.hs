{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.KZG where

import           Control.Monad                              (replicateM)
import           Data.ByteString                            (ByteString, empty)
import           Data.Map.Strict                            (Map, fromList, insert, keys, toList, (!))
import qualified Data.Vector                                as V
import           Data.Vector.Binary                         ()
import           Data.Word                                  (Word8)
import           Prelude                                    hiding (Num (..), length, sum, (/), (^))
import           Test.QuickCheck                            (Arbitrary (..), chooseInt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Protocol.NonInteractiveProof

-- | `d` is the degree of polynomials in the protocol
newtype KZG g1 g2 (d :: Natural) = KZG (ScalarFieldOf g1)
instance Show (ScalarFieldOf g1) => Show (KZG g1 g2 d) where
    show (KZG x) = "KZG " <> show x
instance Eq (ScalarFieldOf g1) => Eq (KZG g1 g2 d) where
    KZG x == KZG y = x == y
instance Arbitrary (ScalarFieldOf g1) => Arbitrary (KZG g1 g2 d) where
    arbitrary = KZG <$> arbitrary

newtype WitnessKZG g1 g2 d = WitnessKZG
  { runWitness :: Map (ScalarFieldOf g1) (V.Vector (PolyVec (ScalarFieldOf g1) d)) }
instance (Show (ScalarFieldOf g1)) => Show (WitnessKZG g1 g2 d) where
    show (WitnessKZG w) = "WitnessKZG " <> show w
instance
  ( KnownNat d
  , Arbitrary (ScalarFieldOf g1)
  , Ord (ScalarFieldOf g1)
  , Ring (ScalarFieldOf g1)
  ) => Arbitrary (WitnessKZG g1 g2 d) where
    arbitrary = do
        n <- chooseInt (1, 3)
        m <- chooseInt (1, 5)
        WitnessKZG . fromList <$> replicateM n ((,) <$> arbitrary <*> (V.fromList <$> replicateM m arbitrary))

-- TODO (Issue #18): check list lengths
instance forall f g1 g2 gt d kzg core.
    ( KZG g1 g2 d ~ kzg
    , KnownNat d
    , Ord f
    , Binary f
    , FiniteField f
    , AdditiveGroup f
    , f ~ ScalarFieldOf g1
    , Binary g1
    , Pairing g1 g2 gt
    , Eq gt
    , CoreFunction g1 core
    ) => NonInteractiveProof (KZG g1 g2 d) core where
    type Transcript (KZG g1 g2 d)  = ByteString
    type SetupProve (KZG g1 g2 d)  = V.Vector g1
    type SetupVerify (KZG g1 g2 d) = (V.Vector g1, g2, g2)
    type Witness (KZG g1 g2 d)     = WitnessKZG g1 g2 d
    type Input (KZG g1 g2 d)       = Map (ScalarFieldOf g1) (V.Vector g1, V.Vector (ScalarFieldOf g1))
    type Proof (KZG g1 g2 d)       = Map (ScalarFieldOf g1) g1

    setupProve :: kzg -> SetupProve kzg
    setupProve (KZG x) =
        let d  = value @d
            xs = V.fromList $ map (x^) [0..d-!1]
            gs = fmap (`scale` pointGen @g1) xs
        in gs

    setupVerify :: kzg -> SetupVerify kzg
    setupVerify (KZG x) =
        let d  = value @d
            xs = V.fromList $ map (x^) [0..d-!1]
            gs = fmap (`scale` pointGen @g1) xs
        in (gs, pointGen @g2, x `scale` pointGen @g2)

    prove :: SetupProve kzg
          -> Witness kzg
          -> (Input kzg, Proof kzg)
    prove gs (WitnessKZG w) = snd $ foldl proveOne (empty, (mempty, mempty)) (toList w)
        where
            proveOne :: (Transcript kzg, (Input kzg, Proof kzg))
                     -> (f, V.Vector (PolyVec f d))
                     -> (Transcript kzg, (Input kzg, Proof kzg))
            proveOne (ts0, (iMap, pMap)) (z, fs) = (ts3, (insert z (cms, fzs) iMap, insert z (gs `com` h) pMap))
                where
                    com = msm @g1 @core
                    cms  = fmap (com gs) fs
                    fzs  = fmap (`evalPolyVec` z) fs

                    ts1 = ts0 `transcript` z `transcript` fzs `transcript` cms
                    (gamma, ts2) = challenges ts1 (fromIntegral $ V.length cms)
                    ts3 = ts2 `transcript` (0 :: Word8)

                    h            = sum $ V.zipWith scalePV (V.fromList gamma) $ fmap (`provePolyVecEval` z) fs

    verify :: SetupVerify kzg -> Input kzg -> Proof kzg -> Bool
    verify (gs, h0, h1) input proof =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (zero, zero)) $ keys input
                p1 = pairing e0 h0
                p2 = pairing e1 h1
            in p1 == p2
        where
            prepareVerifyOne
                :: (Map f (V.Vector g1, V.Vector f), Map f g1)
                -> (Transcript kzg, (g1, g1))
                -> f
                -> (Transcript kzg, (g1, g1))
            prepareVerifyOne (iMap, pMap) (ts0, (v0, v1)) z = (ts3, (v0 + v0', v1 + v1'))
                where
                    (cms, fzs) = iMap ! z
                    w          = pMap ! z

                    ts1 = ts0 `transcript` z `transcript` fzs `transcript` cms
                    (gamma', ts2) = challenges ts1 (fromIntegral $ V.length cms)

                    ts3 = ts2 `transcript` (0 :: Word8)
                    r   = challenge ts3

                    gamma = V.fromList gamma'

                    com = msm @g1 @core

                    v0' = r `scale` sum (V.zipWith scale gamma cms)
                        - r `scale` (gs `com` toPolyVec @f @d [sum $ V.zipWith (*) gamma fzs])
                        + (r * z) `scale` w
                    v1' = r `scale` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size f . (KnownNat size, FiniteField f, Eq f) => PolyVec f size -> f -> PolyVec f size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) `polyVecDiv` toPolyVec [negate z, one]
