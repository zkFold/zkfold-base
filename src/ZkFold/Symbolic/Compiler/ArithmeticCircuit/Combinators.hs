module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    boolCheckC,
    isZeroC,
    invertC,
    plusMultC,
) where

import           Control.Monad.State                                       (execState)
import           Data.Bool                                                 (bool)
import           Prelude                                                   hiding (negate, (*), (+), (-))

import           ZkFold.Base.Algebra.Basic.Class

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Arithmetic, ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint

boolCheckC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @boolCheckC r@ computes @r (r - 1)@ in one PLONK constraint.
boolCheckC r = circuit $ do
    i <- runCircuit r
    newAssigned (\x -> x i * (x i - one))

isZeroC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
isZeroC r = circuit $ fst <$> runInvert r

invertC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
invertC r = flip execState r $ snd <$> runInvert r

runInvert :: (Arithmetic a, MonadBlueprint i a m) => ArithmeticCircuit a -> m (i, i)
runInvert r = do
    i <- runCircuit r
    j <- newConstrained (\x j -> x i * x j) (bool zero one . (== zero) . ($ i))
    k <- newConstrained (\x k -> x i * x k + x j - one) (invert . ($ i))
    return (j, k)

plusMultC :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @plusMult a b c@ computes @a + b * c@ in one PLONK constraint.
plusMultC a b c = circuit $ do
    i <- runCircuit a
    j <- runCircuit b
    k <- runCircuit c
    newAssigned (\x -> x i + x j * x k)
