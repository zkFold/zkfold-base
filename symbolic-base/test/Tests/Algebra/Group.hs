{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use -"                  #-}

module Tests.Algebra.Group (specAdditiveGroup) where

import           Data.Data                                   (Typeable, typeOf)
import           Prelude                                     hiding (Fractional (..), Num (..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.BN254
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519   (Ed25519_Point)
import           ZkFold.Base.Algebra.EllipticCurve.Pasta     (Pallas_Point, Vesta_Point)
import           ZkFold.Base.Algebra.EllipticCurve.PlutoEris (Eris_Point, Pluto_Point)
import           ZkFold.Base.Algebra.EllipticCurve.Secp256k1 (Secp256k1_Point)

specAdditiveGroup' :: forall a . (AdditiveGroup a, Eq a, Show a, Arbitrary a, Typeable a) => Spec
specAdditiveGroup' = do
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

specAdditiveGroup :: Spec
specAdditiveGroup = do
    specAdditiveGroup' @BN254_G1_Point
    specAdditiveGroup' @BN254_G2_Point

    specAdditiveGroup' @BLS12_381_G1_Point
    specAdditiveGroup' @BLS12_381_G2_Point

    specAdditiveGroup' @Pallas_Point
    specAdditiveGroup' @Vesta_Point

    specAdditiveGroup' @Secp256k1_Point

    specAdditiveGroup' @Ed25519_Point

    specAdditiveGroup' @Pluto_Point
    specAdditiveGroup' @Eris_Point
