{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.UInt (specUInt) where

import           Control.Applicative              ((<*>))
import           Control.Monad                    (return)
import           Data.Function                    (($))
import           Data.Functor                     ((<$>))
import           Data.List                        ((++))
import           Numeric.Natural                  (Natural)
import           Prelude                          (div, fmap, show)
import qualified Prelude                          as Haskell
import           System.IO                        (IO)
import           Test.Hspec                       (describe, hspec)
import           Test.QuickCheck                  (Gen, Property, (===))
import           Tests.ArithmeticCircuit          (eval', it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                   (chooseNatural)
import           ZkFold.Symbolic.Compiler         (ArithmeticCircuit)
import qualified ZkFold.Symbolic.Data.Algebra     as Alg
import           ZkFold.Symbolic.Data.UInt

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

eval :: forall a n . UInt n (ArithmeticCircuit a) -> UInt n a
eval (UInt xs x) = UInt (fmap eval' xs) (eval' x)

type Binary a = a -> a -> a

type UBinary n a = Binary (UInt n a)

isHom :: (KnownNat n, PrimeField (Zp p)) => UBinary n (Zp p) -> UBinary n (ArithmeticCircuit (Zp p)) -> Natural -> Natural -> Property
isHom f g x y = eval (Alg.fromNatural x `g` Alg.fromNatural y) === Alg.fromNatural x `f` Alg.fromNatural y

specUInt :: forall p n . (PrimeField (Zp p), KnownNat n) => IO ()
specUInt = hspec $ do
    let n = value @n
        m = 2 Haskell.^ n Haskell.- 1
    describe ("UInt" ++ show n ++ " specification") $ do
        it "Zp embeds Integer" $ do
            x <- toss m
            return $ toNatural @(UInt n (Zp p)) (Alg.fromNatural x) === x
        it "Integer embeds Zp" $ \(x :: UInt n (Zp p)) ->
            Alg.fromNatural (toNatural x) === x
        it "AC embeds Integer" $ do
            x <- toss m
            return $ eval @(Zp p) @n (Alg.fromNatural x) === Alg.fromNatural x
        it "adds correctly" $ isHom @n @p (+) (+) <$> toss m <*> toss m
        it "has zero" $ eval @(Zp p) @n zero === zero
        it "negates correctly" $ do
            x <- toss m
            return $ eval @(Zp p) @n (negate (Alg.fromNatural x)) === negate (Alg.fromNatural x)
        it "subtracts correctly" $ isHom @n @p (-) (-) <$> toss m <*> toss m
        it "multiplies correctly" $ isHom @n @p (Alg.*) (Alg.*) <$> toss m <*> toss m
        it "has one" $ eval @(Zp p) @n Alg.one === Alg.one
        it "strictly adds correctly" $ do
            x <- toss m
            isHom @n @p strictAdd strictAdd x <$> toss (m Haskell.- x)
        it "strictly subtracts correctly" $ do
            x <- toss m
            isHom @n @p strictSub strictSub x <$> toss x
        it "strictly multiplies correctly" $ do
            x <- toss m
            isHom @n @p strictMul strictMul x <$> toss (m `div` x)
