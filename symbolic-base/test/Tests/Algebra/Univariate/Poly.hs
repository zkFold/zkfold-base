{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Algebra.Univariate.Poly (specUnivariatePoly) where

import           Data.Data                                   (typeOf)
import qualified Data.Vector                                 as V
import           Prelude                                     hiding (Fractional (..), Num (..), (^))
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.Polynomials.Univariate  (Poly, fromPoly, toPoly)
import           ZkFold.Prelude

-- TODO: derive naive multiplication for univariate polynomials from multivariate polynomial multiplication
naive :: (Eq a, Field a) => Poly a -> Poly a -> Poly a
naive l r = toPoly $ V.fromList $ go (V.toList (fromPoly l)) (V.toList (fromPoly r))
  where
      go [] _      = []
      go (x:xs) ys = zipWithDefault (+) zero zero (map (x *) ys) (zero : go xs ys)

propMultiplication :: (Eq a, Field a) => (Poly a, Poly a) -> Bool
propMultiplication (p1, p2) = p1 * p2 == p1 `naive` p2

specUnivariatePoly :: Spec
specUnivariatePoly = do
    describe "Univariate polynomials multiplication" $ do
        describe ("Type: " ++ show (typeOf @(Poly (Zp BLS12_381_Scalar)) zero)) $
            describe "Roots of unity can be calculated" $ do
                it "should correctly multiply polynomials" $ do
                    property $ propMultiplication @(Zp BLS12_381_Scalar)
        describe ("Type: " ++ show (typeOf @(Poly Fq12) zero)) $
            describe "No roots of unity (SLOW)" $ do
                it "should correctly multiply polynomials" $ do
                    property $ propMultiplication @Fq12

