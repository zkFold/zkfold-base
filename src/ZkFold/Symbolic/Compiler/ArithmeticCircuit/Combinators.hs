{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    boolCheckC,
    embed,
    expansion,
    splitExpansion,
    gorner,
    isZeroC,
    invertC,
    plusMultC,
) where

import           Data.Foldable                                             (foldlM)
import           Data.Traversable                                          (for)
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
embed x = circuit $ newAssigned $ const (x `scale` one)

expansion :: MonadBlueprint i a m => Integer -> i -> m [i]
expansion n k = do
    bits <- bitsOf n k
    k' <- gorner bits
    constraint (\x -> x k - x k')
    return bits

splitExpansion :: MonadBlueprint i a m => Integer -> Integer -> i -> m (i, i)
splitExpansion n1 n2 k = do
    bits <- bitsOf (n1 + n2) k
    let (lo, hi) = splitAt n1 bits
    l <- gorner lo
    h <- gorner hi
    constraint (\x -> x k - x l - scale ((one + one) ^ n1) (x h))
    return (l, h)

bitsOf :: MonadBlueprint i a m => Integer -> i -> m [i]
bitsOf n k = for [0 .. n - 1] $ \j ->
    newConstrained (\x i -> x i * (x i - one)) ((!! j) . repr . ($ k))
    where
        repr :: forall b . (BinaryExpansion b, Finite b) => b -> [b]
        repr = padBits (numberOfBits @b) . binaryExpansion

gorner :: MonadBlueprint i a m => [i] -> m i
gorner bits = case reverse bits of
    []       -> newAssigned zero
    (b : bs) -> foldlM (\i j -> newAssigned (\x -> x i + x i + x j)) b bs

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
      isZero :: forall a b . WitnessField a b => a -> a
      isZero x = bool @(Bool a) zero one (x == zero)

plusMultC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @plusMult a b c@ computes @a + b * c@ in one PLONK constraint.
plusMultC a b c = circuit $ do
    i <- runCircuit a
    j <- runCircuit b
    k <- runCircuit c
    newAssigned (\x -> x i + x j * x k)
