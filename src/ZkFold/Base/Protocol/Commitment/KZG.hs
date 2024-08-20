{-# LANGUAGE AllowAmbiguousTypes  #-}
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
import           Prelude                                    hiding (Num (..), length, sum, (/), (^))
import           Test.QuickCheck                            (Arbitrary (..), chooseInt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Protocol.NonInteractiveProof

-- | `d` is the degree of polynomials in the protocol
data KZG c1 c2 (d :: Natural) core =
    CoreFunction c1 core =>
    KZG (ScalarField c1)
instance Show (ScalarField c1) => Show (KZG c1 c2 d core) where
    show (KZG x) = "KZG " <> show x
instance Eq (ScalarField c1) => Eq (KZG c1 c2 d core) where
    KZG x == KZG y = x == y
instance (Arbitrary (ScalarField c1), CoreFunction c1 core) => Arbitrary (KZG c1 c2 d core) where
    arbitrary = KZG <$> arbitrary

newtype WitnessKZG c1 c2 d = WitnessKZG { runWitness :: Map (ScalarField c1) (V.Vector (PolyVec (ScalarField c1) d)) }
instance (Show (ScalarField c1)) => Show (WitnessKZG c1 c2 d) where
    show (WitnessKZG w) = "WitnessKZG " <> show w
instance (EllipticCurve c1, f ~ ScalarField c1, KnownNat d, Ring f, Arbitrary f, Ord f) => Arbitrary (WitnessKZG c1 c2 d) where
    arbitrary = do
        n <- chooseInt (1, 3)
        m <- chooseInt (1, 5)
        WitnessKZG . fromList <$> replicateM n ((,) <$> arbitrary <*> (V.fromList <$> replicateM m arbitrary))

instance (KZG c1 c2 d ~ kzg, NonInteractiveProof kzg, Arbitrary kzg, Arbitrary (Witness kzg)) =>
    Arbitrary (NonInteractiveProofTestData (KZG c1 c2 d)) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

-- TODO (Issue #18): check list lengths
instance forall (c1 :: Type) (c2 :: Type) d kzg f g1 core.
    ( KZG c1 c2 d core ~ kzg
    , ScalarField c1 ~ f
    , Point c1 ~ g1
    , KnownNat d
    , Ord (ScalarField c1)
    , Binary (ScalarField c1)
    , FiniteField (ScalarField c1)
    , AdditiveGroup (BaseField c1)
    , Binary (Point c1)
    , Pairing c1 c2
    , CoreFunction c1 core
    ) => NonInteractiveProof (KZG c1 c2 d core) where
    type Transcript (KZG c1 c2 d core)  = ByteString
    type SetupProve (KZG c1 c2 d core)  = V.Vector (Point c1)
    type SetupVerify (KZG c1 c2 d core) = (V.Vector (Point c1), Point c2, Point c2)
    type Witness (KZG c1 c2 d core)     = WitnessKZG c1 c2 d
    type Input (KZG c1 c2 d core)       = Map (ScalarField c1) (V.Vector (Point c1), V.Vector (ScalarField c1))
    type Proof (KZG c1 c2 d core)       = Map (ScalarField c1) (Point c1)

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
          -> Witness kzg
          -> (Input kzg, Proof kzg)
    prove gs (WitnessKZG w) = snd $ foldl proveOne (empty, (mempty, mempty)) (toList w)
        where
            proveOne :: (Transcript kzg, (Input kzg, Proof kzg))
                     -> (f, V.Vector (PolyVec f d))
                     -> (Transcript kzg, (Input kzg, Proof kzg))
            proveOne (ts, (iMap, pMap)) (z, fs) = (ts'', (insert z (cms, fzs) iMap, insert z (gs `com` h) pMap))
                where
                    com = com' @c1 @core
                    cms  = fmap (com gs) fs
                    fzs  = fmap (`evalPolyVec` z) fs

                    (gamma, ts') = flip challenges (fromIntegral $ V.length cms) $ ts
                        `transcript` z
                        `transcript` fzs
                        `transcript` cms
                    h            = sum $ V.zipWith scalePV (V.fromList gamma) $ fmap (`provePolyVecEval` z) fs
                    ts''         = if ts == empty then ts' else snd $ challenge @(Transcript kzg) @f ts'

    verify :: SetupVerify kzg -> Input kzg -> Proof kzg -> Bool
    verify (gs, h0, h1) input proof =
            let (e0, e1) = snd $ foldl (prepareVerifyOne (input, proof)) (empty, (inf, inf)) $ keys input
                p1 = pairing e0 h0
                p2 = pairing e1 h1
            in p1 == p2
        where
            prepareVerifyOne
                :: (Map f (V.Vector g1, V.Vector f), Map f g1)
                -> (Transcript kzg, (g1, g1))
                -> ScalarField c1
                -> (Transcript kzg, (g1, g1))
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

                    com = com' @c1 @core

                    v0' = r `mul` sum (V.zipWith mul gamma cms)
                        - r `mul` (gs `com` toPolyVec @(ScalarField c1) @d [sum $ V.zipWith (*) gamma fzs])
                        + (r * z) `mul` w
                    v1' = r `mul` w

------------------------------------ Helper functions ------------------------------------

provePolyVecEval :: forall size f . (KnownNat size, FiniteField f, Eq f) => PolyVec f size -> f -> PolyVec f size
provePolyVecEval f z = (f - toPolyVec [negate $ f `evalPolyVec` z]) `polyVecDiv` toPolyVec [negate z, one]

class (EllipticCurve curve) => CoreFunction curve core where
    com' :: (f ~ ScalarField curve) => V.Vector (Point curve) -> PolyVec f size -> Point curve


data HaskellCore

instance (EllipticCurve curve, f ~ ScalarField curve) => CoreFunction curve HaskellCore where
    com' gs f = sum $ V.zipWith mul (fromPolyVec f) gs
