{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    boolCheckC,
    embed,
    isZeroC,
    invertC,
    plusMultC,
) where

import           Prelude                                                   hiding (Bool, Eq (..), negate, (*), (+), (-))

import           ZkFold.Base.Algebra.Basic.Class

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Arithmetic, ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Eq                                   (Eq(..))
import           ZkFold.Symbolic.Data.Conditional                          (Conditional(..))
import           ZkFold.Symbolic.Data.Bool                                 (Bool)

boolCheckC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @boolCheckC r@ computes @r (r - 1)@ in one PLONK constraint.
boolCheckC r = circuit $ do
    i <- runCircuit r
    newAssigned (\x -> x i * (x i - one))

embed :: Arithmetic a => a -> ArithmeticCircuit a
embed x = circuit $ newAssigned $ const (x `scale` one)

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
