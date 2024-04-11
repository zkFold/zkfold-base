{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Tests.Multiplication (specMultiplication) where

import qualified Data.Vector                                 as V
import           Prelude                                     (Bool, Eq (..), IO, map, ($))
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.Polynomials.Univariate  (Poly (..), removeZeros)
import           ZkFold.Prelude

naive :: (Eq a, Field a) => Poly a -> Poly a -> Poly a
naive (P l) (P r) = removeZeros $ P $ V.fromList $ go (V.toList l) (V.toList r)
  where
    go [] _        = []
    go (x : xs) ys = zipWithDefault (+) zero zero (map (x *) ys) (zero : go xs ys)

testOp :: (Eq a, Field a) => (Poly a, Poly a) -> Bool
testOp (p1, p2) = p1 * p2 == p1 `naive` p2

specMultiplication :: IO ()
specMultiplication = hspec $ do
  describe "Univariate polynomials multiplication" $ do
    describe "Roots of unity can be calculated" $ do
      it "should correctly multiply polynomials" $ do
        property $ testOp @(Zp BLS12_381_Scalar)
    describe "No roots of unity" $ do
      it "should correctly multiply polynomials" $ do
        property $ testOp @Fq12
