{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use -"                  #-}

module Tests.Univariate (specUnivariate) where

import           Data.Bool                                  (bool)
import           Data.Data                                  (typeOf)
import           Data.List                                  ((\\), sort)
import           Prelude                                    (abs)
import           Prelude                                    hiding ((^), Num(..), Fractional(..), (!!), length, take, drop)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class

import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Protocol.ARK.Plonk             (Plonk, PlonkMaxPolyDegree)
import           ZkFold.Base.Protocol.Commitment.KZG        (F)
import           ZkFold.Prelude                             (take, length)

-- TODO: make all tests polymorphic in the polynomial type

propToPolyVec :: forall c size . (Ring c, Finite size) => [c] -> Bool
propToPolyVec cs =
    let PV p = toPolyVec @c @size cs
    in length p == order @size

propCastPolyVec :: forall c size size' . (Ring c, Finite size, Finite size', Eq c) => [c] -> Bool
propCastPolyVec cs =
    let n = min (order @size) (order @size')
        cs' = bool cs (take n cs) (length cs > n)
        PV p' = castPolyVec @c @size @size' (toPolyVec @c @size cs')
    in length p' == order @size'

propPolyVecDivision :: forall c size . (Field c, Finite size, Eq c) => PolyVec c size -> PolyVec c size -> Bool
propPolyVecDivision p q = 
    let d1 = deg $ vec2poly p
        d2 = deg $ vec2poly q
    in (p * q) / q == p || (d1 + d2 > order @size - 1)

propPolyVecZero :: Integer -> Bool
propPolyVecZero i =
    let omega = rootOfUnity 5 :: F
        p = polyVecZero @F @Plonk @PlonkMaxPolyDegree
        x = omega^abs i
    in p `evalPolyVec` x == zero

propPolyVecLagrange :: Integer -> Bool
propPolyVecLagrange i =
    let omega = rootOfUnity 5 :: F
        p = polyVecLagrange @F @Plonk @PlonkMaxPolyDegree i omega
    in p `evalPolyVec` (omega^i) == one && 
        all ((== zero) . (p `evalPolyVec`) . (omega^)) ([1 .. order @Plonk] \\ [i])

propPolyVecGrandProduct :: (Field c, Finite size, Ord c) => PolyVec c size -> c -> c -> Bool
propPolyVecGrandProduct p beta gamma =
    let PV cs = p
        cs' = sort cs
        p' = PV cs'
        PV zs  = polyVecGrandProduct zero p p' beta gamma
    in last zs * (beta * last cs + gamma) == (beta * last cs' + gamma)

specUnivariate :: IO ()
specUnivariate = hspec $ do
    describe "Univariate polynomials specification" $ do
        describe ("Type: " ++ show (typeOf @(PolyVec F Plonk) zero)) $ do
            describe "toPolyVec" $ do
                it "should return a list of the correct length" $ do
                    property $ propToPolyVec @F @Plonk
            describe "castPolyVec" $ do
                it "should return a list of the correct length" $ do
                    property $ propCastPolyVec @F @Plonk @Plonk
                it "should return a list of the correct length" $ do
                    property $ propCastPolyVec @F @Plonk @PlonkMaxPolyDegree
                it "should return a list of the correct length" $ do
                    property $ propCastPolyVec @F @PlonkMaxPolyDegree @Plonk
            describe "Ring axioms" $ do
                it "should satisfy additive associativity" $ do
                    property $ \(a :: PolyVec F Plonk) b c -> (a + b) + c == a + (b + c)
                it "should satisfy additive commutativity" $ do
                    property $ \(a :: PolyVec F Plonk) b -> a + b == b + a
                it "should satisfy additive identity" $ do
                    property $ \(a :: PolyVec F Plonk) -> a + zero == a
                it "should satisfy additive inverse" $ do
                    property $ \(a :: PolyVec F Plonk) -> a + negate a == zero
                it "should satisfy multiplicative associativity" $ do
                    property $ \(a :: PolyVec F Plonk) b c -> (a * b) * c == a * (b * c)
                it "should satisfy multiplicative commutativity" $ do
                    property $ \(a :: PolyVec F Plonk) b -> a * b == b * a
                it "should satisfy multiplicative identity" $ do
                    property $ \(a :: PolyVec F Plonk) -> a * one == a
                it "should satisfy distributivity" $ do
                    property $ \(a :: PolyVec F Plonk) b c -> a * (b + c) == a * b + a * c
            describe "Polynomial division" $ do
                it "should satisfy the definition" $ do
                    property $ \(p :: PolyVec F Plonk) q -> q /= zero ==> propPolyVecDivision p q
            describe "polyVecZero" $ do
                it "should satisfy the definition" $ do
                    all propPolyVecZero [0 .. order @PlonkMaxPolyDegree - 1] `shouldBe` True
            describe "Lagrange polynomial" $ do
                it "should satisfy the definition" $ do
                    all propPolyVecLagrange [1 .. order @Plonk] `shouldBe` True
            describe "polyVecGrandProduct" $ do
                it "should satisfy the definition" $ do
                    property $ propPolyVecGrandProduct @F @Plonk