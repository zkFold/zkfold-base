{-# LANGUAGE AllowAmbiguousTypes #-}
module Tests.ReedSolomon where

import           Data.Data                                   (typeOf)
import qualified Data.Vector                                 as V
import           Prelude                                     hiding (Fractional (..), Num (..), (^))
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Polynomials.Univariate  (Poly, fromPoly, toPoly)
import           ZkFold.Prelude
import GHC.TypeNats (KnownNat)
import ZkFold.Base.Algorithm.ReedSolomon (generator)
import GHC.Natural (Natural)

propGenerator :: forall n k a. (KnownNat n, KnownNat k, Eq a, Field a) => Bool
propGenerator = fromPoly (generator @n @k @a (fromConstant (2 :: Natural)) ) == fromPoly zero

specReedSolomon :: IO ()
specReedSolomon = hspec $ do
    describe "Reed-Solomon" $ do
        it "generator function is correct" $ do
            property $ propGenerator @15 @9 @(Zp 15)