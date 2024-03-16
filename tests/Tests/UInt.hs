{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.UInt (specUInt) where

import           Control.Monad                   (return)
import           Data.Data                       (Proxy (..))
import           Data.Function                   (($))
import           Data.List                       (map, (++))
import           GHC.TypeNats                    (KnownNat, natVal)
import           Prelude                         (Integer, div, show)
import qualified Prelude                         as Haskell
import           System.IO                       (IO)
import           Test.Hspec                      (describe, hspec)
import           Test.QuickCheck                 (Gen, chooseInteger, (===))
import           Tests.ArithmeticCircuit         (eval', it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Compiler        (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.UInt

toss :: Integer -> Gen Integer
toss x = chooseInteger (0, x)

value :: forall a n . UInt n (ArithmeticCircuit a) -> UInt n a
value (UInt xs x) = UInt (map eval' xs) (eval' x)

specUInt :: forall p n . (Prime p, KnownNat n) => IO ()
specUInt = hspec $ do
    let n = Haskell.toInteger $ natVal (Proxy :: Proxy n)
    describe ("UInt" ++ show n ++ " specification") $ do
        it "Zp embeds Integer" $ do
            x <- toss (2 ^ n - 1)
            return $ toInteger @p @n (fromConstant x) === x
        it "Integer embeds Zp" $ \(x :: UInt n (Zp p)) ->
            fromConstant (toInteger x) === x
        it "AC embeds Integer" $ do
            x <- toss (2 ^ n - 1)
            return $ value @(Zp p) @n (fromConstant x) === fromConstant x
        it "adds correctly" $ do
            x <- toss (2 ^ n - 1)
            y <- toss (2 ^ n - 1 - x)
            return $ value @(Zp p) @n (fromConstant x + fromConstant y)
                === fromConstant x + fromConstant y
        it "has zero" $ value @(Zp p) @n zero === zero
        it "negates correctly" $ value @(Zp p) @n (negate zero) === negate zero
        it "subtracts correctly" $ do
            x <- toss (2 ^ n - 1)
            y <- toss x
            return $ value @(Zp p) @n (fromConstant x - fromConstant y)
                === fromConstant x - fromConstant y
        it "multiplies correctly" $ do
            x <- toss (2 ^ n - 1)
            y <- toss ((2 ^ n - 1) `div` x)
            return $ value @(Zp p) @n (fromConstant x * fromConstant y)
                === fromConstant x * fromConstant y
        it "has one" $ value @(Zp p) @n one === one
