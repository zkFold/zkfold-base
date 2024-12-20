{-# LANGUAGE AllowAmbiguousTypes #-}
module Tests.ReedSolomon where

import           GHC.Natural                                (Natural)
import           Prelude                                    hiding (Fractional (..), Num (..), (^))
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Polynomials.Univariate (fromPoly)
import           ZkFold.Base.Algorithm.ReedSolomon          (generator)

propGenerator :: (Field c, Eq c) => Natural -> Natural -> c -> Bool
propGenerator k n a = fromPoly (generator k n a ) == fromPoly zero

specReedSolomon :: IO ()
specReedSolomon = hspec $ do
    describe "Reed-Solomon" $ do
        it "generator function is correct" $ do
            property $ propGenerator 17 9 (fromConstant (2 :: Natural) :: Zp 17)
