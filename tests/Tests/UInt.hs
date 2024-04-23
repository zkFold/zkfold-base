{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.UInt (specUInt) where

import           Control.Applicative              ((<*>))
import           Control.Monad                    (return)
import           Data.Function                    (($))
import           Data.Functor                     ((<$>))
import           Data.List                        (map, (++))
import           Numeric.Natural                  (Natural)
import           Prelude                          (div, fmap, show)
import           System.IO                        (IO)
import           Test.Hspec                       (describe, hspec)
import           Test.QuickCheck                  (Gen, Property, (===))
import           Tests.ArithmeticCircuit          (eval', it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                   (chooseNatural)
import           ZkFold.Symbolic.Compiler         (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.UInt

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

eval :: forall a n . UInt n (ArithmeticCircuit a) -> UInt n a
eval (UInt xs x) = UInt (fmap eval' xs) (eval' x)

type Binary a = a -> a -> a

type UBinary n a = Binary (UInt n a)

isHom :: (KnownNat n, Prime p) => UBinary n (Zp p) -> UBinary n (ArithmeticCircuit (Zp p)) -> Natural -> Natural -> Property
isHom f g x y = eval (fromConstant x `g` fromConstant y) === fromConstant x `f` fromConstant y

specUInt :: forall p n . (Prime p, KnownNat n) => IO ()
specUInt = hspec $ do
    let n = value @n
        m = 2 ^ n -! 1
    describe ("UInt" ++ show n ++ " specification") $ do
        it "Zp embeds Integer" $ do
            x <- toss m
            return $ toConstant @(UInt n (Zp p)) (fromConstant x) === x
        it "Integer embeds Zp" $ \(x :: UInt n (Zp p)) ->
            fromConstant (toConstant @_ @Natural x) === x
        it "AC embeds Integer" $ do
            x <- toss m
            return $ eval @(Zp p) @n (fromConstant x) === fromConstant x
        it "adds correctly" $ isHom @n @p (+) (+) <$> toss m <*> toss m
        it "has zero" $ eval @(Zp p) @n zero === zero
        it "negates correctly" $ do
            x <- toss m
            return $ eval @(Zp p) @n (negate (fromConstant x)) === negate (fromConstant x)
        it "subtracts correctly" $ isHom @n @p (-) (-) <$> toss m <*> toss m
        it "multiplies correctly" $ isHom @n @p (*) (*) <$> toss m <*> toss m
        it "has one" $ eval @(Zp p) @n one === one
        it "strictly adds correctly" $ do
            x <- toss m
            isHom @n @p strictAdd strictAdd x <$> toss (m -! x)
        it "strictly subtracts correctly" $ do
            x <- toss m
            isHom @n @p strictSub strictSub x <$> toss x
        it "strictly multiplies correctly" $ do
            x <- toss m
            isHom @n @p strictMul strictMul x <$> toss (m `div` x)
