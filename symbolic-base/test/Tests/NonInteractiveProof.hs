{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.NonInteractiveProof (specNonInteractiveProof) where

import           Data.ByteString                             (ByteString)
import           Data.Typeable                               (Proxy (..), Typeable, typeRep)
import           GHC.Generics                                (U1)
import           Prelude                                     hiding (Fractional (..), Num (..), length)
import           Test.Hspec                                  (describe, hspec, it)
import           Test.QuickCheck                             (Arbitrary, Testable (property), withMaxSuccess)

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Protocol.KZG                    (KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof    (HaskellCore, NonInteractiveProof (..))
import           ZkFold.Base.Protocol.Plonk                  (Plonk)
import           ZkFold.Base.Protocol.Plonkup                (Plonkup)

propNonInteractiveProof :: forall a core . (NonInteractiveProof a core) => (a, Witness a) -> Bool
propNonInteractiveProof (a, w) =
    let sp = setupProve @a @core a
        sv = setupVerify @a @core a
        (i, p) = prove @a @core sp w
    in verify @a @core sv i p

specNonInteractiveProof' :: forall a core . (Typeable a, NonInteractiveProof a core,
    Show a, Show (Witness a), Arbitrary a, Arbitrary (Witness a)) => IO ()
specNonInteractiveProof' = hspec $ do
    describe "Non-interactive proof protocol specification (SLOW)" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ withMaxSuccess 10 $ property $ propNonInteractiveProof @a @core

specNonInteractiveProof :: IO ()
specNonInteractiveProof = do
    specNonInteractiveProof' @(KZG BLS12_381_G1 BLS12_381_G2 32) @HaskellCore
    specNonInteractiveProof' @(Plonk 1 U1 32 2 BLS12_381_G1 BLS12_381_G2 ByteString) @HaskellCore
    specNonInteractiveProof' @(Plonkup 1 U1 32 2 BLS12_381_G1 BLS12_381_G2 ByteString) @HaskellCore
