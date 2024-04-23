{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.ByteString (specByteString) where

import           Control.Applicative              ((<*>))
import           Control.Monad                    (return)
import           Data.Function                    (($))
import           Data.Functor                     ((<$>))
import           GHC.TypeNats                     (Mod, type (<=))
import           Numeric.Natural                  (Natural)
import           Prelude                          (show, type (~), (<>), fmap)
import qualified Prelude                          as Haskell
import           System.IO                        (IO)
import           Test.Hspec                       (Spec, describe, hspec)
import           Test.QuickCheck                  (Gen, Property, chooseInteger, (===))
import           Tests.ArithmeticCircuit          (eval', it)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                   (chooseNatural)
import           ZkFold.Symbolic.Compiler         (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators (Iso (..))
import           ZkFold.Symbolic.Data.UInt

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

eval :: forall a n . ByteString n (ArithmeticCircuit a) -> ByteString n a
eval (ByteString x xs) = ByteString (eval' x) (fmap eval' xs)

type Binary a = a -> a -> a

type UBinary n a = Binary (ByteString n a)

isHom :: (KnownNat n, Prime p) => UBinary n (Zp p) -> UBinary n (ArithmeticCircuit (Zp p)) -> Natural -> Natural -> Property
isHom f g x y = eval (fromConstant x `g` fromConstant y) === fromConstant x `f` fromConstant y

isRightNeutral
    :: (KnownNat n, Prime p)
    => UBinary n (Zp p)
    -> UBinary n (ArithmeticCircuit (Zp p))
    -> ByteString n (Zp p)
    -> ByteString n (ArithmeticCircuit (Zp p))
    -> Natural
    -> Property
isRightNeutral f g n1 n2 x = eval (fromConstant x `g` n2) === fromConstant x `f` n1

isLeftNeutral
    :: (KnownNat n, Prime p)
    => UBinary n (Zp p)
    -> UBinary n (ArithmeticCircuit (Zp p))
    -> ByteString n (Zp p)
    -> ByteString n (ArithmeticCircuit (Zp p))
    -> Natural
    -> Property
isLeftNeutral f g n1 n2 x = eval (n2 `g` fromConstant x) === n1 `f` fromConstant x

testWords
    :: forall n wordSize p
    .  KnownNat n
    => Prime p
    => KnownNat wordSize
    => ToWords (ByteString n (ArithmeticCircuit (Zp p))) (ByteString wordSize (ArithmeticCircuit (Zp p)))
    => ToWords (ByteString n (Zp p)) (ByteString wordSize (Zp p))
    => Spec
testWords = it ("divides a bytestring of length " <> show (value @n) <> " into words of length " <> show (value @wordSize)) $ do
    x <- toss m
    let arithBS = fromConstant x :: ByteString n (ArithmeticCircuit (Zp p))
        zpBS = fromConstant x :: ByteString n (Zp p)
    return (Haskell.fmap eval (toWords arithBS :: [ByteString wordSize (ArithmeticCircuit (Zp p))]) === toWords zpBS)
    where
        n = Haskell.toInteger $ value @n
        m = 2 Haskell.^ n -! 1

testTruncate
    :: forall n m p
    .  KnownNat n
    => Prime p
    => KnownNat m
    => Truncate (ByteString n (ArithmeticCircuit (Zp p))) (ByteString m (ArithmeticCircuit (Zp p)))
    => Truncate (ByteString n (Zp p)) (ByteString m (Zp p))
    => Spec
testTruncate = it ("truncates a bytestring of length " <> show (value @n) <> " to length " <> show (value @m)) $ do
    x <- toss m
    let arithBS = fromConstant x :: ByteString n (ArithmeticCircuit (Zp p))
        zpBS = fromConstant x :: ByteString n (Zp p)
    return (eval (truncate arithBS :: ByteString m (ArithmeticCircuit (Zp p))) === truncate zpBS)
    where
        n = Haskell.toInteger $ value @n
        m = 2 Haskell.^ n -! 1

testGrow
    :: forall n m p
    .  KnownNat n
    => Prime p
    => KnownNat m
    => Extend (ByteString n (ArithmeticCircuit (Zp p))) (ByteString m (ArithmeticCircuit (Zp p)))
    => Extend (ByteString n (Zp p)) (ByteString m (Zp p))
    => Spec
testGrow = it ("extends a bytestring of length " <> show (value @n) <> " to length " <> show (value @m)) $ do
    x <- toss m
    let arithBS = fromConstant x :: ByteString n (ArithmeticCircuit (Zp p))
        zpBS    = fromConstant x :: ByteString n (Zp p)
    return (eval (extend arithBS :: ByteString m (ArithmeticCircuit (Zp p))) === extend zpBS)
    where
        n = Haskell.toInteger $ value @n
        m = 2 Haskell.^ n -! 1

-- | For some reason, Haskell can't infer obvious type relations such as n <= n + 1...
--
specByteString
    :: forall p n
    .  Prime p
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
    => n <= 3 * n
    => Mod n 1 ~ 0
    => Mod n 2 ~ 0
    => Mod n 4 ~ 0
    => Mod n n ~ 0
    => Mod (3 * n) n ~ 0
    => KnownNat (3 * n)
    => KnownNat (n + 1)
    => KnownNat (n + 10)
    => KnownNat (n + 128)
    => KnownNat (n + n)
    => IO ()
specByteString = hspec $ do
    let n = Haskell.fromIntegral $ value @n
        m = 2 Haskell.^ n -! 1
    describe ("ByteString" <> show n <> " specification") $ do

        it "Zp embeds Integer" $ do
            x <- toss m
            return $ toConstant @(ByteString n (Zp p)) (fromConstant x) === x
        it "Integer embeds Zp" $ \(x :: ByteString n (Zp p)) ->
            fromConstant (toConstant @_ @Natural x) === x
        it "AC embeds Integer" $ do
            x <- toss m
            return $ eval @(Zp p) @n (fromConstant x) === fromConstant x
        it "applies sum modulo n via UInt correctly" $ do
            x <- toss m
            y <- toss m

            let acX :: ByteString n (ArithmeticCircuit (Zp p)) = fromConstant x
                acY :: ByteString n (ArithmeticCircuit (Zp p)) = fromConstant y

                acSum :: ByteString n (ArithmeticCircuit (Zp p)) = from $ from acX + (from acY :: UInt n (ArithmeticCircuit (Zp p)))

                zpSum :: ByteString n (Zp p) = fromConstant $ x + y


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
            shift <- chooseInteger (-3 * n, 3 * n)
            x <- toss m
            return $ eval @(Zp p) @n (shiftBits (fromConstant x) shift) === (shiftBits (fromConstant x) shift)
        it "performs bit rotations correctly" $ do
            shift <- chooseInteger (-3 * n, 3 * n)
            x <- toss m
            return $ eval @(Zp p) @n (rotateBits (fromConstant x) shift) === (rotateBits (fromConstant x) shift)
        testWords @n @1 @p
        testWords @n @2 @p
        testWords @n @4 @p
        testWords @n @n @p
        it "concatenates bytestrings correctly" $ do
            x <- toss m
            y <- toss m
            z <- toss m
            let ac = concat $ fromConstant @Natural @(ByteString n (ArithmeticCircuit (Zp p))) <$> [x, y, z]
                zp = concat $ fromConstant @Natural @(ByteString n (Zp p)) <$> [x, y, z]
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
