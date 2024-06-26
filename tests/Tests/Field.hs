{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use -"                  #-}

module Tests.Field (specField) where

import           Data.Data                                   (Typeable, typeOf)
import           Prelude                                     hiding (Fractional (..), Num (..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381

specField' :: forall a . (Field a, Eq a, Show a, Arbitrary a, Typeable a) => IO ()
specField' = hspec $ do
    describe "Field specification" $ do
        describe ("Type: " ++ show (typeOf @a zero)) $ do
            describe "Field axioms" $ do
                it "should satisfy additive associativity" $ do
                    property $ \(a :: a) b c -> (a + b) + c == a + (b + c)
                it "should satisfy additive commutativity" $ do
                    property $ \(a :: a) b -> a + b == b + a
                it "should satisfy additive identity" $ do
                    property $ \(a :: a) -> a + zero == a
                it "should satisfy additive inverse" $ do
                    property $ \(a :: a) -> a + negate a == zero
                it "should satisfy multiplicative associativity" $ do
                    property $ \(a :: a) b c -> (a * b) * c == a * (b * c)
                it "should satisfy multiplicative commutativity" $ do
                    property $ \(a :: a) b -> a * b == b * a
                it "should satisfy multiplicative identity" $ do
                    property $ \(a :: a) -> a * one == a
                it "should satisfy multiplicative inverse" $ do
                    property $ \(a :: a) -> a /= zero ==> a * finv a == one
                it "should satisfy distributivity" $ do
                    property $ \(a :: a) b c -> a * (b + c) == a * b + a * c

specField :: IO ()
specField = do
    specField' @Fr
    specField' @Fq
    specField' @Fq2
    specField' @Fq6
    specField' @Fq12