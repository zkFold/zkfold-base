{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use -"                  #-}

module Tests.Group (specAdditiveGroup) where

import           Data.Data                                        (Typeable, typeOf)
import           Prelude                                          hiding (Fractional (..), Num (..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.BN254
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Pasta          (Pallas, Vesta)
import           ZkFold.Base.Protocol.IVC.CycleFold.NativeContext (ForeignPoint(..))
import           ZkFold.Base.Protocol.IVC.Oracle                  (MiMCHash)
import           ZkFold.Symbolic.Interpreter                      (Interpreter(..))

specAdditiveGroup' :: forall a . (AdditiveGroup a, Eq a, Show a, Arbitrary a, Typeable a) => IO ()
specAdditiveGroup' = hspec $ do
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

specAdditiveGroup :: IO ()
specAdditiveGroup = do
    -- specAdditiveGroup' @(Point BN254_G1)
    -- specAdditiveGroup' @(Point BN254_G2)

    -- specAdditiveGroup' @(Point BLS12_381_G1)
    -- specAdditiveGroup' @(Point BLS12_381_G2)

    -- specAdditiveGroup' @(Point Pallas)
    -- specAdditiveGroup' @(Point Vesta)

    specAdditiveGroup' @(ForeignPoint MiMCHash 2 1 (ScalarField Pallas) (Interpreter (ScalarField Pallas)))
