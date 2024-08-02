{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.ByteString (specByteString) where

import           Control.Applicative                         ((<*>))
import           Control.Monad                               (return)
import           Data.Function                               (($))
import           Data.Functor                                ((<$>))
import           Data.List                                   ((++))
import           Prelude                                     (show, type (~), (<>))
import qualified Prelude                                     as Haskell
import           System.IO                                   (IO)
import           Test.Hspec                                  (Spec, describe, hspec)
import           Test.QuickCheck                             (Gen, Property, chooseInteger, withMaxSuccess, (===))
import           Tests.ArithmeticCircuit                     (it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, exec)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators            (Extend (..), Iso (..), RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Interpreter                 (Interpreter (Interpreter))

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

eval :: forall a n . ByteString n (ArithmeticCircuit a) -> ByteString n (Interpreter a)
eval (ByteString bits) = ByteString $ Interpreter (exec bits)

type Binary a = a -> a -> a

type UBinary n b = Binary (ByteString n b)

isHom :: (KnownNat n, PrimeField (Zp p)) => UBinary n (Interpreter (Zp p)) -> UBinary n (ArithmeticCircuit (Zp p)) -> Natural -> Natural -> Property
isHom f g x y = eval (fromConstant x `g` fromConstant y) === fromConstant x `f` fromConstant y

isRightNeutral
    :: (KnownNat n, PrimeField (Zp p))
    => UBinary n (Interpreter (Zp p))
    -> UBinary n (ArithmeticCircuit (Zp p))
    -> ByteString n (Interpreter (Zp p))
    -> ByteString n (ArithmeticCircuit (Zp p))
    -> Natural
    -> Property
isRightNeutral f g n1 n2 x = eval (fromConstant x `g` n2) === fromConstant x `f` n1

isLeftNeutral
    :: (KnownNat n, PrimeField (Zp p))
    => UBinary n (Interpreter (Zp p))
    -> UBinary n (ArithmeticCircuit (Zp p))
    -> ByteString n (Interpreter (Zp p))
    -> ByteString n (ArithmeticCircuit (Zp p))
    -> Natural
    -> Property
isLeftNeutral f g n1 n2 x = eval (n2 `g` fromConstant x) === n1 `f` fromConstant x

testWords
    :: forall n wordSize p
    .  KnownNat n
    => PrimeField (Zp p)
    => KnownNat wordSize
    => ToWords (ByteString n (ArithmeticCircuit (Zp p))) (ByteString wordSize (ArithmeticCircuit (Zp p)))
    => ToWords (ByteString n (Interpreter (Zp p))) (ByteString wordSize (Interpreter (Zp p)))
    => Spec
testWords = it ("divides a bytestring of length " <> show (value @n) <> " into words of length " <> show (value @wordSize)) $ do
    x <- toss m
    let arithBS = fromConstant x :: ByteString n (ArithmeticCircuit (Zp p))
        zpBS = fromConstant x :: ByteString n (Interpreter (Zp p))
    return (Haskell.fmap eval (toWords arithBS :: [ByteString wordSize (ArithmeticCircuit (Zp p))]) === toWords zpBS)
    where
        n = Haskell.toInteger $ value @n
        m = 2 Haskell.^ n -! 1

testTruncate
    :: forall n m p
    .  KnownNat n
    => PrimeField (Zp p)
    => KnownNat m
    => Truncate (ByteString n (ArithmeticCircuit (Zp p))) (ByteString m (ArithmeticCircuit (Zp p)))
    => Truncate (ByteString n (Interpreter (Zp p))) (ByteString m (Interpreter (Zp p)))
    => Spec
testTruncate = it ("truncates a bytestring of length " <> show (value @n) <> " to length " <> show (value @m)) $ do
    x <- toss m
    let arithBS = fromConstant x :: ByteString n (ArithmeticCircuit (Zp p))
        zpBS = fromConstant x :: ByteString n (Interpreter (Zp p))
    return (eval (truncate arithBS :: ByteString m (ArithmeticCircuit (Zp p))) === truncate zpBS)
    where
        n = Haskell.toInteger $ value @n
        m = 2 Haskell.^ n -! 1

testGrow
    :: forall n m p
    .  KnownNat n
    => PrimeField (Zp p)
    => KnownNat m
    => Extend (ByteString n (ArithmeticCircuit (Zp p))) (ByteString m (ArithmeticCircuit (Zp p)))
    => Extend (ByteString n (Interpreter (Zp p))) (ByteString m (Interpreter (Zp p)))
    => Spec
testGrow = it ("extends a bytestring of length " <> show (value @n) <> " to length " <> show (value @m)) $ do
    x <- toss m
    let arithBS = fromConstant x :: ByteString n (ArithmeticCircuit (Zp p))
        zpBS    = fromConstant x :: ByteString n (Interpreter (Zp p))
    return (eval (extend arithBS :: ByteString m (ArithmeticCircuit (Zp p))) === extend zpBS)
    where
        n = Haskell.toInteger $ value @n
        m = 2 Haskell.^ n -! 1

-- | For some reason, Haskell can't infer obvious type relations such as n <= n + 1...
--
specByteString'
    :: forall p n
    .  PrimeField (Zp p)
    => KnownNat n
    => 1 <= n
    => 2 <= n
    => 4 <= n
    => 8 <= n
    => 16 <= n
    => 32 <= n
    => n <= n + 1
    => n <= n + 10
    => n <= n + 128
    => n <= n + n
    => Mod n 1 ~ 0
    => Mod n 2 ~ 0
    => Mod n 4 ~ 0
    => Mod n n ~ 0
    => Mod (3 * n) n ~ 0
    => (Div (3 * n) n) * n ~ 3 * n
    => (Div n n) * n ~ n
    => (Div n 4) * 4 ~ n
    => (Div n 2) * 2 ~ n
    => KnownNat (3 * n)
    => KnownNat (n + 1)
    => KnownNat (n + 10)
    => KnownNat (n + 128)
    => KnownNat (n + n)
    => IO ()
specByteString' = hspec $ do
    let n = Haskell.fromIntegral $ value @n
        m = 2 Haskell.^ n -! 1
    describe ("ByteString" ++ show n ++ " specification") $ do

        it "Zp embeds Integer" $ do
            x <- toss m
            return $ toConstant @(ByteString n (Interpreter (Zp p))) (fromConstant x) === x
        it "Integer embeds Zp" $ \(x :: ByteString n (Interpreter (Zp p))) ->
            fromConstant (toConstant @_ @Natural x) === x
        it "AC embeds Integer" $ do
            x <- toss m
            return $ eval @(Zp p) @n (fromConstant x) === fromConstant x

        -- TODO: remove withMaxSuccess when eval is optimised
        it "applies sum modulo n via UInt correctly" $ withMaxSuccess 10 $ do
            x <- toss m
            y <- toss m

            let acX :: ByteString n (ArithmeticCircuit (Zp p)) = fromConstant x
                acY :: ByteString n (ArithmeticCircuit (Zp p)) = fromConstant y

                acSum :: ByteString n (ArithmeticCircuit (Zp p)) = from $ from acX + (from acY :: UInt n Auto (ArithmeticCircuit (Zp p)))

                zpSum :: ByteString n (Interpreter (Zp p)) = fromConstant $ x + y


            return $ eval acSum === zpSum
        it "applies bitwise OR correctly" $ isHom @n @p (||) (||) <$> toss m <*> toss m
        it "applies bitwise XOR correctly" $ isHom @n @p xor xor <$> toss m <*> toss m
        it "has false" $ eval @(Zp p) @n false === false
        it "obeys left neutrality for OR" $ isLeftNeutral @n @p (||) (||) false false <$> toss m
        it "obeys right neutrality for OR" $ isRightNeutral @n @p (||) (||) false false <$> toss m
        it "obeys left neutrality for XOR" $ isLeftNeutral @n @p xor xor false false <$> toss m
        it "obeys right neutrality for XOR" $ isRightNeutral @n @p xor xor false false <$> toss m
        it "applies bitwise NOT correctly" $ do
            x <- toss m
            return $ eval @(Zp p) @n (not (fromConstant x)) === not (fromConstant x)
        it "Applies bitwise AND correctly" $ isHom @n @p (&&) (&&) <$> toss m <*> toss m
        it "has true" $ eval @(Zp p) @n true === true
        it "obeys left multiplicative neutrality" $ isLeftNeutral @n @p (&&) (&&) true true <$> toss m
        it "obeys right multiplicative neutrality" $ isRightNeutral @n @p (&&) (&&) true true <$> toss m
        it "performs bit shifts correctly" $ do
            shift <- chooseInteger ((-3) * n, 3 * n)
            x <- toss m
            return $ eval @(Zp p) @n (shiftBits (fromConstant x) shift) === shiftBits (fromConstant x) shift
        it "performs bit rotations correctly" $ do
            shift <- chooseInteger ((-3) * n, 3 * n)
            x <- toss m
            return $ eval @(Zp p) @n (rotateBits (fromConstant x) shift) === rotateBits (fromConstant x) shift
        testWords @n @1 @p
        testWords @n @2 @p
        testWords @n @4 @p
        testWords @n @n @p
        it "concatenates bytestrings correctly" $ do
            x <- toss m
            y <- toss m
            z <- toss m
            let acs = fromConstant @Natural @(ByteString n (ArithmeticCircuit (Zp p))) <$> [x, y, z]
                zps = fromConstant @Natural @(ByteString n (Interpreter (Zp p))) <$> [x, y, z]
            let ac = concat acs :: ByteString (3 * n) (ArithmeticCircuit (Zp p))
                zp = concat zps
            return $ eval @(Zp p) @(3 * n) ac === zp
        testTruncate @n @1 @p
        testTruncate @n @4 @p
        testTruncate @n @8 @p
        testTruncate @n @16 @p
        testTruncate @n @32 @p
        testTruncate @n @n @p
        testGrow @n @(n + 1) @p
        testGrow @n @(n + 10) @p
        testGrow @n @(n + 128) @p
        testGrow @n @(n + n) @p

specByteString :: IO ()
specByteString = do
    specByteString' @BLS12_381_Scalar @32
    specByteString' @BLS12_381_Scalar @512
    specByteString' @BLS12_381_Scalar @508 -- Twice the number of bits encoded by BLS12_381_Scalar.
