{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.UInt (specUInt) where

import           Control.Applicative              ((<*>))
import           Control.Monad                    (return)
import           Data.Function                    (($))
import           Data.Functor                     ((<$>))
import           Data.List                        ((++))
import           Numeric.Natural                  (Natural)
import           Prelude                          (show)
import qualified Prelude                          as P
import           System.IO                        (IO)
import           Test.Hspec                       (describe, hspec)
import           Test.QuickCheck                  (Gen, Property, (.&.), (===))
import           Tests.ArithmeticCircuit          (eval, it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                   (chooseNatural)
import           ZkFold.Symbolic.Compiler         (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Combinators (Extend (..), Shrink (..))
import           ZkFold.Symbolic.Data.Compare
import           ZkFold.Symbolic.Data.UInt


toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

type Binary a = a -> a -> a

type UBinary n a = Binary (UInt n a)

isHom :: (KnownNat n, PrimeField (Zp p)) => UBinary n (Zp p) -> UBinary n (ArithmeticCircuit (Zp p)) -> Natural -> Natural -> Property
isHom f g x y = eval (fromConstant x `g` fromConstant y) === fromConstant x `f` fromConstant y

specUInt :: forall p n . (PrimeField (Zp p), KnownNat n, KnownNat (2 * n), n <= (2 * n)) => IO ()
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
            return $ eval @(Zp p) @(UInt n) (fromConstant x) === fromConstant x
        it "adds correctly" $ isHom @n @p (+) (+) <$> toss m <*> toss m
        it "has zero" $ eval @(Zp p) @(UInt n) zero === zero
        it "negates correctly" $ do
            x <- toss m
            return $ eval @(Zp p) @(UInt n) (negate (fromConstant x)) === negate (fromConstant x)
        it "subtracts correctly" $ isHom @n @p (-) (-) <$> toss m <*> toss m
        it "multiplies correctly" $ isHom @n @p (*) (*) <$> toss m <*> toss m

        -- TODO: Optimise eval and uncomment this test
        {--
        it "performs divMod correctly" $ do
            n <- toss m
            d <- toss m
            let (acQ, acR) = (fromConstant n :: UInt n (ArithmeticCircuit (Zp p))) `divMod` (fromConstant d)
            let (zpQ, zpR) = (fromConstant n :: UInt n (Zp p)) `divMod` (fromConstant d)
            return $ (eval acQ, eval acR) === (zpQ, zpR)
        --}

        -- TODO: Optimise eval and test eea on ArithmeticCircuits
        it "calculates gcd correctly" $ do
            x <- toss m
            y <- toss m
            let (_, _, r) = eea (fromConstant x :: UInt n (Zp p)) (fromConstant y)
                ans = fromConstant (P.gcd x y) :: UInt n (Zp p)
            return $ r === ans
        it "calculates Bezout coefficients correctly" $ do
            x' <- toss m
            y' <- toss m
            let x = x' `P.div` (P.gcd x' y')
                y = y' `P.div` (P.gcd x' y')

                -- We will test Bezout coefficients by multiplying two UInts less than 2^n, hence we need 2^(2n) bits to store the result
                zpX = fromConstant x :: UInt (2 * n) (Zp p)
                zpY = fromConstant y
                (s, t, _) = eea zpX zpY
            -- if x and y are coprime, s is the multiplicative inverse of x modulo y and t is the multiplicative inverse of y modulo x
            return $ ((zpX * s) `mod` zpY === one) .&. ((zpY * t) `mod` zpX === one)
        it "has one" $ eval @(Zp p) @(UInt n) one === one
        it "strictly adds correctly" $ do
            x <- toss m
            isHom @n @p strictAdd strictAdd x <$> toss (m -! x)
        it "strictly subtracts correctly" $ do
            x <- toss m
            isHom @n @p strictSub strictSub x <$> toss x
        it "strictly multiplies correctly" $ do
            x <- toss m
            isHom @n @p strictMul strictMul x <$> toss (m `P.div` x)

        it "extends correctly" $ do
            x <- toss m
            let acUint = fromConstant x :: UInt n (ArithmeticCircuit (Zp p))
                zpUint = fromConstant x :: UInt (2 * n) (Zp p)
            return $ eval @(Zp p) (extend acUint :: UInt (2 * n) (ArithmeticCircuit (Zp p))) === zpUint

        it "shrinks correctly" $ do
            x <- toss (m * m)
            let acUint = fromConstant x :: UInt (2 * n) (ArithmeticCircuit (Zp p))
                zpUint = fromConstant x :: UInt n (Zp p)
            return $ eval @(Zp p) (shrink acUint :: UInt n (ArithmeticCircuit (Zp p))) === zpUint

        it "checks equality" $ do
            x <- toss m
            let acUint = fromConstant x :: UInt n (ArithmeticCircuit (Zp p))
            let acEq = eval @(Zp p) (acUint == acUint)
            return $ acEq === true

        it "checks inequality" $ do
            x <- toss m
            y' <- toss m
            let y = if y' P.== x then x + 1 else y'

            let acUint1 = fromConstant x :: UInt n (ArithmeticCircuit (Zp p))
                acUint2 = fromConstant y :: UInt n (ArithmeticCircuit (Zp p))
                acEq = eval @(Zp p) (acUint1 == acUint2)

            return $ acEq === false

        it "checks greater than" $ do
            x <- toss m
            y <- toss m
            let x' = fromConstant x :: UInt n (Zp p)
                y' = fromConstant y :: UInt n (Zp p)
                x'' = fromConstant x :: UInt n (ArithmeticCircuit (Zp p))
                y'' = fromConstant y :: UInt n (ArithmeticCircuit (Zp p))
                gt' = x' > y'
                gt'' = eval (x'' > y'')
            return $ gt' === gt''
