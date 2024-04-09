{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use -"                  #-}

module Tests.Univariate (specUnivariate) where

import Data.Bool (bool)
import Data.Data (typeOf)
import Data.List ((\\))
import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Intro as VA
import Numeric.Natural (Natural)
import Test.Hspec
import Test.QuickCheck
import Tests.Plonk (PlonkMaxPolyDegreeBS, PlonkSizeBS)
import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Number
import ZkFold.Base.Algebra.Polynomials.Univariate
import ZkFold.Base.Protocol.ARK.Plonk (F)
import ZkFold.Prelude (length, take)
import Prelude (abs)
import Prelude hiding (Fractional (..), Num (..), drop, length, take, (!!), (^))

-- TODO (Issue #22): remove dependencies from KZG and Plonk
-- TODO (Issue #22): make all tests polymorphic in the polynomial type

propToPolyVec :: forall c size. (Ring c, KnownNat size) => [c] -> Bool
propToPolyVec cs =
  let PV p = toPolyVec @c @size $ V.fromList cs
   in length p == value @size

propCastPolyVec :: forall c size size'. (Ring c, KnownNat size, KnownNat size', Eq c) => [c] -> Bool
propCastPolyVec cs =
  let n = min (value @size) (value @size')
      cs' = V.fromList $ bool cs (take n cs) (length cs > n)
      PV p' = castPolyVec @c @size @size' (toPolyVec @c @size cs')
   in length p' == value @size'

propPolyVecDivision :: forall c size. (Field c, KnownNat size, Eq c) => PolyVec c size -> PolyVec c size -> Bool
propPolyVecDivision p q =
  let d1 = deg $ vec2poly p
      d2 = deg $ vec2poly q
   in (p * q) / q == p || (d1 + d2 > fromIntegral (value @size) - 1)

propPolyVecZero :: Natural -> Bool
propPolyVecZero i =
  let Just omega = rootOfUnity 5 :: Maybe F
      p = polyVecZero @F @PlonkSizeBS @PlonkMaxPolyDegreeBS
      x = omega ^ abs i
   in p `evalPolyVec` x == zero

propPolyVecLagrange :: Natural -> Bool
propPolyVecLagrange i =
  let Just omega = rootOfUnity 5 :: Maybe F
      p = polyVecLagrange @F @PlonkSizeBS @PlonkMaxPolyDegreeBS i omega
   in p `evalPolyVec` (omega ^ i) == one
        && all ((== zero) . (p `evalPolyVec`) . (omega ^)) ([1 .. value @PlonkSizeBS] \\ [i])

propPolyVecGrandProduct :: (Field c, KnownNat size, Ord c) => PolyVec c size -> c -> c -> Bool
propPolyVecGrandProduct p beta gamma =
  let PV cs = p
      cs' = V.modify VA.sort cs
      p' = PV cs'
      PV zs = polyVecGrandProduct zero p p' beta gamma
   in V.last zs * (beta * V.last cs + gamma) == (beta * V.last cs' + gamma)

specUnivariate :: IO ()
specUnivariate = hspec $ do
  describe "Univariate polynomials specification" $ do
    describe ("Type: " ++ show (typeOf @(PolyVec F PlonkSizeBS) zero)) $ do
      describe "toPolyVec" $ do
        it "should return a list of the correct length" $ do
          property $ propToPolyVec @F @PlonkSizeBS
      describe "castPolyVec" $ do
        it "should return a list of the correct length" $ do
          property $ propCastPolyVec @F @PlonkSizeBS @PlonkSizeBS
        it "should return a list of the correct length" $ do
          property $ propCastPolyVec @F @PlonkSizeBS @PlonkMaxPolyDegreeBS
        it "should return a list of the correct length" $ do
          property $ propCastPolyVec @F @PlonkMaxPolyDegreeBS @PlonkSizeBS
      describe "Ring axioms" $ do
        it "should satisfy additive associativity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) b c -> (a + b) + c == a + (b + c)
        it "should satisfy additive commutativity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) b -> a + b == b + a
        it "should satisfy additive identity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) -> a + zero == a
        it "should satisfy additive inverse" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) -> a + negate a == zero
        it "should satisfy multiplicative associativity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) b c -> (a * b) * c == a * (b * c)
        it "should satisfy multiplicative commutativity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) b -> a * b == b * a
        it "should satisfy multiplicative identity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) -> a * one == a
        it "should satisfy distributivity" $ do
          property $ \(a :: PolyVec F PlonkSizeBS) b c -> a * (b + c) == a * b + a * c
      describe "Polynomial division" $ do
        it "should satisfy the definition" $ do
          property $ \(p :: PolyVec F PlonkSizeBS) q -> q /= zero ==> propPolyVecDivision p q
      describe "polyVecZero" $ do
        it "should satisfy the definition" $ do
          all propPolyVecZero [0 .. value @PlonkMaxPolyDegreeBS - 1] `shouldBe` True
      describe "Lagrange polynomial" $ do
        it "should satisfy the definition" $ do
          all propPolyVecLagrange [1 .. value @PlonkSizeBS] `shouldBe` True
      describe "polyVecGrandProduct" $ do
        it "should satisfy the definition" $ do
          property $ propPolyVecGrandProduct @F @PlonkSizeBS
