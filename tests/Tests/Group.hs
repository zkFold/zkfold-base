{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use -"                  #-}

module Tests.Group (specAdditiveGroup) where

import Data.Data (Typeable, typeOf)
import Test.Hspec
import Test.QuickCheck
import ZkFold.Base.Algebra.Basic.Class
import Prelude hiding (Fractional (..), Num (..), length)

specAdditiveGroup :: forall a. (AdditiveGroup a, Eq a, Show a, Arbitrary a, Typeable a) => IO ()
specAdditiveGroup = hspec $ do
  describe "Group specification" $ do
    describe ("Type: " ++ show (typeOf @a zero)) $ do
      describe "Additive group axioms" $ do
        it "should satisfy additive associativity" $ do
          property $ \(a :: a) b c -> (a + b) + c == a + (b + c)
        it "should satisfy additive commutativity" $ do
          property $ \(a :: a) b -> a + b == b + a
        it "should satisfy additive identity" $ do
          property $ \(a :: a) -> a + zero == a
        it "should satisfy additive inverse" $ do
          property $ \(a :: a) -> a + negate a == zero
