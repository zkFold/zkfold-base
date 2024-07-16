{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module Tests.UInt (specUInt) where

import           Control.Applicative                         ((<*>))
import           Control.Monad                               (return)
import           Data.Function                               (($))
import           Data.Functor                                ((<$>))
import           Data.List                                   ((++))
import           Numeric.Natural                             (Natural)
import           Prelude                                     (show, type (~))
import qualified Prelude                                     as P
import           System.IO                                   (IO)
import           Test.Hspec                                  (describe, hspec)
import           Test.QuickCheck                             (Gen, Property, withMaxSuccess, (.&.), (===))
import           Tests.ArithmeticCircuit                     (exec1, it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector                     (Vector, item)
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, exec)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Combinators            (Extend (..), NumberOfRegisters, Shrink (..))
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.UInt

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

evalBool :: forall a . Bool (ArithmeticCircuit 1 a) -> Bool a
evalBool (Bool ac) = Bool $ exec1 ac

evalBoolVec :: forall a . Bool (Vector 1 a) -> Bool a
evalBoolVec (Bool v) = Bool $ item v

execAcUint :: forall a n . UInt n ArithmeticCircuit a -> Vector (NumberOfRegisters a n) a
execAcUint (UInt v) = exec v

execZpUint :: forall a n . UInt n Vector a -> Vector (NumberOfRegisters a n) a
execZpUint (UInt v) = v

type Binary a = a -> a -> a

type UBinary n b a = Binary (UInt n b a)

isHom :: (KnownNat n, PrimeField (Zp p)) => UBinary n Vector (Zp p) -> UBinary n ArithmeticCircuit (Zp p) -> Natural -> Natural -> Property
isHom f g x y = execAcUint (fromConstant x `g` fromConstant y) === execZpUint (fromConstant x `f` fromConstant y)

specUInt'
    :: forall p n r r2n
    .  PrimeField (Zp p)
    => KnownNat n
    => KnownNat (2 * n)
    => n <= 2 * n
    => r ~ NumberOfRegisters (Zp p) n
    => r2n ~ NumberOfRegisters (Zp p) (2 * n)
    => 1 <= r
    => 1 <= r2n
    => KnownNat r
    => KnownNat (r + r)
    => KnownNat r2n
    => KnownNat (r2n + r2n)
    => KnownNat (r - 1)
    => KnownNat (r2n - 1)
    => 1 + (r - 1) ~ r
    => 1 + (r2n - 1) ~ r2n
    => IO ()
specUInt' = hspec $ do
    let n = value @n
        m = 2 ^ n -! 1
    describe ("UInt" ++ show n ++ " specification") $ do
        it "Zp embeds Integer" $ do
            x <- toss m
            return $ toConstant @(UInt n Vector (Zp p)) (fromConstant x) === x
        it "Integer embeds Zp" $ \(x :: UInt n Vector (Zp p)) ->
            fromConstant (toConstant @_ @Natural x) === x
        it "AC embeds Integer" $ do
            x <- toss m
            return $ execAcUint @(Zp p) @n (fromConstant x) === execZpUint @_ @n (fromConstant x)
        it "adds correctly" $ isHom @n @p (+) (+) <$> toss m <*> toss m
        it "has zero" $ execAcUint @(Zp p) @n zero === execZpUint @_ @n zero
        it "negates correctly" $ do
            x <- toss m
            return $ execAcUint @(Zp p) @n (negate (fromConstant x)) === execZpUint @_ @n (negate (fromConstant x))
        it "subtracts correctly" $ isHom @n @p (-) (-) <$> toss m <*> toss m
        it "multiplies correctly" $ isHom @n @p (*) (*) <$> toss m <*> toss m

        -- TODO: Optimise exec and uncomment this test
        {--
        it "performs divMod correctly" $ do
            n <- toss m
            d <- toss m
            let (acQ, acR) = (fromConstant n :: UInt n ArithmeticCircuit (Zp p)) `divMod` (fromConstant d)
            let (zpQ, zpR) = (fromConstant n :: UInt n Vector (Zp p)) `divMod` (fromConstant d)
            return $ (execAcUint acQ, execAcUint acR) === (execZpUint zpQ, execZpUint zpR)
        --}

        it "calculates gcd correctly" $ withMaxSuccess 10 $ do
            x <- toss m
            y <- toss m
            let (_, _, r) = eea (fromConstant x :: UInt n Vector (Zp p)) (fromConstant y)
                ans = fromConstant (P.gcd x y) :: UInt n Vector (Zp p)
            return $ r === ans
        it "calculates Bezout coefficients correctly" $ withMaxSuccess 10 $ do
            x' <- toss m
            y' <- toss m
            let x = x' `P.div` P.gcd x' y'
                y = y' `P.div` P.gcd x' y'

                -- We will test Bezout coefficients by multiplying two UInts less than 2^n, hence we need 2^(2n) bits to store the result
                zpX = fromConstant x :: UInt (2 * n) Vector (Zp p)
                zpY = fromConstant y
                (s, t, _) = eea zpX zpY
            -- if x and y are coprime, s is the multiplicative inverse of x modulo y and t is the multiplicative inverse of y modulo x
            return $ ((zpX * s) `mod` zpY === one) .&. ((zpY * t) `mod` zpX === one)
        it "has one" $ execAcUint @(Zp p) @n one === execZpUint @_ @n one
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
            let acUint = fromConstant x :: UInt n ArithmeticCircuit (Zp p)
                zpUint = fromConstant x :: UInt (2 * n) Vector (Zp p)
            return $ execAcUint @(Zp p) (extend acUint :: UInt (2 * n) ArithmeticCircuit (Zp p)) === execZpUint zpUint

        it "shrinks correctly" $ do
            x <- toss (m * m)
            let acUint = fromConstant x :: UInt (2 * n) ArithmeticCircuit (Zp p)
                zpUint = fromConstant x :: UInt n Vector (Zp p)
            return $ execAcUint @(Zp p) (shrink acUint :: UInt n ArithmeticCircuit (Zp p)) === execZpUint zpUint

        it "checks equality" $ do
            x <- toss m
            let acUint = fromConstant x :: UInt n ArithmeticCircuit (Zp p)
            return $ evalBool @(Zp p) (acUint == acUint) === Bool one

        it "checks inequality" $ do
            x <- toss m
            y' <- toss m
            let y = if y' P.== x then x + 1 else y'

            let acUint1 = fromConstant x :: UInt n ArithmeticCircuit (Zp p)
                acUint2 = fromConstant y :: UInt n ArithmeticCircuit (Zp p)

            return $ evalBool @(Zp p) (acUint1 == acUint2) === Bool zero

        it "checks greater than" $ do
            x <- toss m
            y <- toss m
            let x' = fromConstant x  :: UInt n Vector (Zp p)
                y' = fromConstant y  :: UInt n Vector (Zp p)
                x'' = fromConstant x :: UInt n ArithmeticCircuit (Zp p)
                y'' = fromConstant y :: UInt n ArithmeticCircuit (Zp p)
                gt' = evalBoolVec $ x' > y'
                gt'' = evalBool @(Zp p) (x'' > y'')
            return $ gt' === gt''

specUInt :: IO ()
specUInt = do
    specUInt' @BLS12_381_Scalar @32
    specUInt' @BLS12_381_Scalar @500
