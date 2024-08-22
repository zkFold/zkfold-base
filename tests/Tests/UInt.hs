{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module Tests.UInt (specUInt) where

import           Control.Applicative                         ((<*>))
import           Control.Monad                               (return, when)
import           Data.Function                               (($))
import           Data.Functor                                ((<$>))
import           Data.List                                   ((++))
import           GHC.Generics                                (Par1 (Par1), U1)
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
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, exec)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Combinators            (Extend (..), KnownRegisterSize, NumberOfRegisters,
                                                              RegisterSize (..), Shrink (..))
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Interpreter                 (Interpreter (Interpreter))

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

evalBool :: forall a . Bool (ArithmeticCircuit a U1) -> a
evalBool (Bool ac) = exec1 ac

evalBoolVec :: forall a . Bool (Interpreter a) -> a
evalBoolVec (Bool (Interpreter (Par1 v))) = v

execAcUint :: forall a n r . UInt n r (ArithmeticCircuit a U1) -> Vector (NumberOfRegisters a n r) a
execAcUint (UInt v) = exec v

execZpUint :: forall a n r . UInt n r (Interpreter a) -> Vector (NumberOfRegisters a n r) a
execZpUint (UInt (Interpreter v)) = v

type Binary a = a -> a -> a

type UBinary n b r = Binary (UInt n b r)

isHom :: (KnownNat n, PrimeField (Zp p), KnownRegisterSize r) => UBinary n r (Interpreter (Zp p)) -> UBinary n r (ArithmeticCircuit (Zp p) U1) -> Natural -> Natural -> Property
isHom f g x y = execAcUint (fromConstant x `g` fromConstant y) === execZpUint (fromConstant x `f` fromConstant y)

specUInt'
    :: forall p n r r2n rs
    .  PrimeField (Zp p)
    => KnownNat n
    => KnownNat (2 * n)
    => KnownRegisterSize rs
    => n <= 2 * n
    => r ~ NumberOfRegisters (Zp p) n rs
    => r2n ~ NumberOfRegisters (Zp p) (2 * n) rs
    => KnownNat r
    => KnownNat (r + r)
    => KnownNat r2n
    => KnownNat (r2n + r2n)
    => KnownNat (r - 1)
    => KnownNat (r2n - 1)
    => IO ()
specUInt' = hspec $ do
    let n = value @n
        m = 2 ^ n -! 1
    describe ("UInt" ++ show n ++ " specification") $ do
        it "Zp embeds Integer" $ do
            x <- toss m
            return $ toConstant @(UInt n rs (Interpreter (Zp p))) (fromConstant x) === x
        it "Integer embeds Zp" $ \(x :: UInt n rs (Interpreter (Zp p))) ->
            fromConstant (toConstant @_ @Natural x) === x
        it "AC embeds Integer" $ do
            x <- toss m
            return $ execAcUint @(Zp p) @n @rs (fromConstant x) === execZpUint @_ @n @rs (fromConstant x)
        it "adds correctly" $ isHom @n @p @rs (+) (+) <$> toss m <*> toss m
        it "has zero" $ execAcUint @(Zp p) @n @rs zero === execZpUint @_ @n @rs zero
        it "negates correctly" $ do
            x <- toss m
            return $ execAcUint @(Zp p) @n @rs (negate (fromConstant x)) === execZpUint @_ @n @rs (negate (fromConstant x))
        it "subtracts correctly" $ isHom @n @p @rs (-) (-) <$> toss m <*> toss m
        it "multiplies correctly" $ isHom @n @p @rs (*) (*) <$> toss m <*> toss m

        -- TODO: reduce the number of constraints in divMod or wait for lookup arguments
        when (n <= 128) $ it "performs divMod correctly" $ withMaxSuccess 10 $ do
            num <- toss m
            d <- toss m
            let (acQ, acR) = (fromConstant num :: UInt n rs (ArithmeticCircuit (Zp p) U1)) `divMod` (fromConstant d)
            let (zpQ, zpR) = (fromConstant num :: UInt n rs (Interpreter (Zp p))) `divMod` (fromConstant d)
            return $ (execAcUint acQ, execAcUint acR) === (execZpUint zpQ, execZpUint zpR)

        when (n <= 128) $ it "calculates gcd correctly" $ withMaxSuccess 10 $ do
            x <- toss m
            y <- toss m
            let (_, _, r) = eea (fromConstant x :: UInt n rs (Interpreter (Zp p))) (fromConstant y)
                ans = fromConstant (P.gcd x y) :: UInt n rs (Interpreter (Zp p))
            return $ r === ans
        when (n <= 128) $ it "calculates Bezout coefficients correctly" $ withMaxSuccess 10 $ do
            x' <- toss m
            y' <- toss m
            let x = x' `P.div` P.gcd x' y'
                y = y' `P.div` P.gcd x' y'

                -- We will test Bezout coefficients by multiplying two UInts less than 2^n, hence we need 2^(2n) bits to store the result
                zpX = fromConstant x :: UInt (2 * n) rs (Interpreter (Zp p))
                zpY = fromConstant y
                (s, t, _) = eea zpX zpY
            -- if x and y are coprime, s is the multiplicative inverse of x modulo y and t is the multiplicative inverse of y modulo x
            return $ ((zpX * s) `mod` zpY === one) .&. ((zpY * t) `mod` zpX === one)
        it "has one" $ execAcUint @(Zp p) @n @rs one === execZpUint @_ @n @rs one
        it "strictly adds correctly" $ do
            x <- toss m
            isHom @n @p @rs strictAdd strictAdd x <$> toss (m -! x)
        it "strictly subtracts correctly" $ do
            x <- toss m
            isHom @n @p @rs strictSub strictSub x <$> toss x
        it "strictly multiplies correctly" $ do
            x <- toss m
            isHom @n @p @rs strictMul strictMul x <$> toss (m `P.div` x)

        it "extends correctly" $ do
            x <- toss m
            let acUint = fromConstant x :: UInt n rs (ArithmeticCircuit (Zp p) U1)
                zpUint = fromConstant x :: UInt (2 * n) rs (Interpreter (Zp p))
            return $ execAcUint @(Zp p) (extend acUint :: UInt (2 * n) rs (ArithmeticCircuit (Zp p) U1)) === execZpUint zpUint

        it "shrinks correctly" $ do
            x <- toss (m * m)
            let acUint = fromConstant x :: UInt (2 * n) rs (ArithmeticCircuit (Zp p) U1)
                zpUint = fromConstant x :: UInt n rs (Interpreter (Zp p))
            return $ execAcUint @(Zp p) (shrink acUint :: UInt n rs (ArithmeticCircuit (Zp p) U1)) === execZpUint zpUint

        it "checks equality" $ do
            x <- toss m
            let acUint = fromConstant x :: UInt n rs (ArithmeticCircuit (Zp p) U1)
            return $ evalBool @(Zp p) (acUint == acUint) === one

        it "checks inequality" $ do
            x <- toss m
            y' <- toss m
            let y = if y' P.== x then x + 1 else y'

            let acUint1 = fromConstant x :: UInt n rs (ArithmeticCircuit (Zp p) U1)
                acUint2 = fromConstant y :: UInt n rs (ArithmeticCircuit (Zp p) U1)

            return $ evalBool @(Zp p) (acUint1 == acUint2) === zero

        it "checks greater than" $ do
            x <- toss m
            y <- toss m
            let x' = fromConstant x  :: UInt n rs (Interpreter (Zp p))
                y' = fromConstant y  :: UInt n rs (Interpreter (Zp p))
                x'' = fromConstant x :: UInt n rs (ArithmeticCircuit (Zp p) U1)
                y'' = fromConstant y :: UInt n rs (ArithmeticCircuit (Zp p) U1)
                gt' = evalBoolVec $ x' > y'
                gt'' = evalBool @(Zp p) (x'' > y'')
            return $ gt' === gt''

specUInt :: IO ()
specUInt = do
    specUInt' @BLS12_381_Scalar @32 @_ @_ @Auto
    specUInt' @BLS12_381_Scalar @500 @_ @_ @Auto

    specUInt' @BLS12_381_Scalar @32 @_ @_ @(Fixed 10)
    specUInt' @BLS12_381_Scalar @500 @_ @_ @(Fixed 10)
