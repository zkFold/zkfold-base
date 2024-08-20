{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.NonInteractiveProof (specNonInteractiveProof) where

import           Data.Typeable                               (Proxy (..), Typeable, typeRep)
import           Prelude                                     hiding (Fractional (..), Num (..), length)
import           Test.Hspec                                  (describe, hspec, it)
import           Test.QuickCheck                             (Arbitrary, Testable (property), withMaxSuccess)
import           Tests.NonInteractiveProof.Plonk             (PlonkBS, specPlonk)

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Protocol.Commitment.KZG         (KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..),
                                                              NonInteractiveProofTestData (..))

propNonInteractiveProof :: forall a .
    NonInteractiveProof a =>
    NonInteractiveProofTestData a -> Bool
propNonInteractiveProof (TestData a w) =
    let sp = setupProve a
        sv = setupVerify a
        (i, p) = prove @a sp w
    in verify @a sv i p

specNonInteractiveProof' :: forall a . (Typeable a, NonInteractiveProof a,
    Show a, Show (Input a), Show (Witness a),
    Arbitrary (NonInteractiveProofTestData a)) => IO ()
specNonInteractiveProof' = hspec $ do
    describe "Non-interactive proof protocol specification" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ withMaxSuccess 10 $ property $ propNonInteractiveProof @a

specNonInteractiveProof :: IO ()
specNonInteractiveProof = do
    specNonInteractiveProof' @(KZG BLS12_381_G1 BLS12_381_G2 32)

    specPlonk
    specNonInteractiveProof' @(PlonkBS 2)
