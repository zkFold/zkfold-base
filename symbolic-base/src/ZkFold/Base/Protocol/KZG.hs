{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.KZG where

import           Control.Monad                              (replicateM)
import           Data.ByteString                            (ByteString, empty)
import           Data.Kind                                  (Type)
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
newtype KZG field g1 g2 (d :: Natural) = KZG field
instance Show field => Show (KZG field g1 g2 d) where
    show (KZG x) = "KZG " <> show x
instance Eq field => Eq (KZG field g1 g2 d) where
    KZG x == KZG y = x == y
instance Arbitrary field => Arbitrary (KZG field g1 g2 d) where
    arbitrary = KZG <$> arbitrary

newtype WitnessKZG field g1 g2 d = WitnessKZG { runWitness :: Map field (V.Vector (PolyVec field d)) }
instance (Show field) => Show (WitnessKZG field g1 g2 d) where
    show (WitnessKZG w) = "WitnessKZG " <> show w
-- instance
--   ( SubgroupCurve c1 Bool baseField1 scalarField point
--   , SubgroupCurve c2 Bool baseField2 scalarField point
--   , KnownNat d
--   , Arbitrary scalarField
--   , Ord scalarField
--   , g1 ~ point baseField1
--   , g2 ~ point baseField2
--   ) => Arbitrary (WitnessKZG scalarField g1 g2 d) where
--     arbitrary = do
--         n <- chooseInt (1, 3)
--         m <- chooseInt (1, 5)
--         WitnessKZG . fromList <$> replicateM n ((,) <$> arbitrary <*> (V.fromList <$> replicateM m arbitrary))

-- TODO (Issue #18): check list lengths
instance forall c1 c2 (k1 :: Type) k2 pt1 pt2 f g1 g2 gt d kzg core.
    ( KZG f g1 g2 d ~ kzg
    , KnownNat d
    , Ord f
    , Binary f
    , FiniteField f
    , AdditiveGroup f
    , Binary g1
    , Pairing f g1 g2 gt
    , Eq gt
    , SubgroupCurve c2 Bool k2 f pt2
    , CoreFunction c1 k1 f pt1 core
    , pt1 k1 ~ g1
    , pt2 k2 ~ g2
    ) => NonInteractiveProof (KZG f g1 g2 d) core where
    type Transcript (KZG f g1 g2 d)  = ByteString
    type SetupProve (KZG f g1 g2 d)  = V.Vector g1
    type SetupVerify (KZG f g1 g2 d) = (V.Vector g1, g2, g2)
    type Witness (KZG f g1 g2 d)     = WitnessKZG f g1 g2 d
    type Input (KZG f g1 g2 d)       = Map f (V.Vector g1, V.Vector f)
    type Proof (KZG f g1 g2 d)       = Map f g1

    setupProve :: kzg -> SetupProve kzg
    setupProve (KZG x) =
        let d  = value @d
            xs = V.fromList $ map (x^) [0..d-!1]
            g1_gen = pointGen @c1 @Bool @k1 @f @pt1
            gs = fmap (`scale` g1_gen) xs
        in gs

    setupVerify :: kzg -> SetupVerify kzg
    setupVerify (KZG x) =
        let d  = value @d
            xs = V.fromList $ map (x^) [0..d-!1]
            g1_gen = pointGen @c1 @Bool @k1 @f @pt1
            g2_gen = pointGen @c2 @Bool @k2 @f @pt2
            gs = fmap (`scale` g1_gen) xs
        in (gs, g2_gen, x `scale` g2_gen)

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
                    com = msm @c1 @k1 @f @pt1 @core
                    cms  = fmap (com gs) fs
                    fzs  = fmap (`evalPolyVec` z) fs

                    ts1 = ts0 `transcript` z `transcript` fzs `transcript` cms
                    (gamma, ts2) = challenges ts1 (fromIntegral $ V.length cms)
                    ts3 = ts2 `transcript` (0 :: Word8)

                    h            = sum $ V.zipWith scalePV (V.fromList gamma) $ fmap (`provePolyVecEval` z) fs

    verify :: SetupVerify kzg -> Input kzg -> Proof kzg -> Bool
    verify (gs, h0, h1) input proof =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (zero, zero)) $ keys input
                p1 = pairing @f e0 h0
                p2 = pairing @f e1 h1
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

                    com = msm @c1 @k1 @f @pt1 @core

                    v0' = r `scale` sum (V.zipWith scale gamma cms)
                        - r `scale` (gs `com` toPolyVec @f @d [sum $ V.zipWith (*) gamma fzs])
                        + (r * z) `scale` w
                    v1' = r `scale` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size f . (KnownNat size, FiniteField f, Eq f) => PolyVec f size -> f -> PolyVec f size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) `polyVecDiv` toPolyVec [negate z, one]
