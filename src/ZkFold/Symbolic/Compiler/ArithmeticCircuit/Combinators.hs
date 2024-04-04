{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    boolCheckC,
    embed,
    expansion,
    splitExpansion,
    horner,
    isZeroC,
    invertC,
    plusMultC,
) where

import           Data.Foldable                                             (foldlM)
import           Data.Traversable                                          (for)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Bool, Eq (..), negate, splitAt, (!!), (*), (+), (-), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                            (splitAt, (!!))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Arithmetic, ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool                                 (Bool)
import           ZkFold.Symbolic.Data.Conditional                          (Conditional (..))
import           ZkFold.Symbolic.Data.Eq                                   (Eq (..))

boolCheckC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @boolCheckC r@ computes @r (r - 1)@ in one PLONK constraint.
boolCheckC r = circuit $ do
    i <- runCircuit r
    newAssigned (\x -> x i * (x i - one))

embed :: Arithmetic a => a -> ArithmeticCircuit a
embed x = circuit $ newAssigned $ const (fromConstant x)

expansion :: MonadBlueprint i a m => Natural -> i -> m [i]
-- ^ @expansion n k@ computes a binary expansion of @k@ if it fits in @n@ bits.
expansion n k = do
    bits <- bitsOf n k
    k' <- horner bits
    constraint (\x -> x k - x k')
    return bits

splitExpansion :: MonadBlueprint i a m => Natural -> Natural -> i -> m (i, i)
-- ^ @splitExpansion n1 n2 k@ computes two values @(l, h)@ such that
-- @k = 2^n1 h + l@, @l@ fits in @n1@ bits and @h@ fits in n2 bits (if such
-- values exist).
splitExpansion n1 n2 k = do
    bits <- bitsOf (n1 + n2) k
    let (lo, hi) = splitAt n1 bits
    l <- horner lo
    h <- horner hi
    constraint (\x -> x k - x l - scale (2 ^ n1 :: Natural) (x h))
    return (l, h)

bitsOf :: MonadBlueprint i a m => Natural -> i -> m [i]
-- ^ @bitsOf n k@ creates @n@ bits and sets their witnesses equal to @n@ smaller
-- bits of @k@.
bitsOf n k = for [0 .. n -! 1] $ \j ->
    newConstrained (\x i -> x i * (x i - one)) ((!! j) . repr . ($ k))
    where
        repr :: forall b . (BinaryExpansion b, Finite b) => b -> [b]
        repr = padBits (numberOfBits @b) . binaryExpansion

horner :: MonadBlueprint i a m => [i] -> m i
-- ^ @horner [b0,...,bn]@ computes the sum @b0 + 2 b1 + ... + 2^n bn@ using
-- Horner's scheme.
horner xs = case reverse xs of
    []       -> newAssigned (const zero)
    (b : bs) -> foldlM (\a i -> newAssigned (\x -> x i + x a + x a)) b bs

isZeroC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
isZeroC r = circuit $ fst <$> runInvert r

invertC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
invertC r = circuit $ snd <$> runInvert r

runInvert :: MonadBlueprint i a m => ArithmeticCircuit a -> m (i, i)
runInvert r = do
    i <- runCircuit r
    j <- newConstrained (\x j -> x i * x j) (isZero . ($ i))
    k <- newConstrained (\x k -> x i * x k + x j - one) (invert . ($ i))
    return (j, k)
    where
      isZero :: forall a . (Ring a, Eq (Bool a) a, Conditional (Bool a) a) => a -> a
      isZero x = bool @(Bool a) zero one (x == zero)

plusMultC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @plusMult a b c@ computes @a + b * c@ in one PLONK constraint.
plusMultC a b c = circuit $ do
    i <- runCircuit a
    j <- runCircuit b
    k <- runCircuit c
    newAssigned (\x -> x i + x j * x k)
