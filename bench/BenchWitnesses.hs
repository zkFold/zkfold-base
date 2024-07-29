{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE OverloadedLists  #-}

module Main where

import           GHC.Integer                                    (Integer)
import           Data.Foldable                                  (foldl)
import           Data.Function                                  (($), (.), flip)
import           Data.Monoid                                    ((<>))
import           Control.Applicative                            ((<*>))
import           Control.Monad                                  ((>>=))
import           Control.DeepSeq                                (force)
import           Control.Exception                              (evaluate)
import           Data.Functor                                   ((<$>))
import           Text.Show                                      (show)
import           Data.List                                      (reverse)
import           Data.Aeson                                     (ToJSON)
import           Data.String                                    (String)
import           System.IO                                      (IO)
import           System.Random                                  (randomIO)
import           Test.Tasty.Bench                               (Benchmark, env, bench, nf, defaultMain)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector                        hiding (reverse)
import           ZkFold.Prelude
import           ZkFold.Symbolic.Algorithms.Hash.SHA2
import           ZkFold.Symbolic.Algorithms.Hash.MiMC 
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants 
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.Data.UInt

hashCircuit :: forall n p .
   PrimeField (Zp p) =>
   SHA2 "SHA256" (ArithmeticCircuit (Zp p)) n =>
   IO (ByteString 256 (ArithmeticCircuit (Zp p)))
hashCircuit = sha2 @"SHA256" @(ArithmeticCircuit (Zp p)) @n . fromConstant <$> randomIO @Integer

-- | Generate random addition circuit of given size
additionCircuit :: forall n p .
    (KnownNat n, PrimeField (Zp p)) =>
    IO (ByteString n (ArithmeticCircuit (Zp p)))
additionCircuit = from @(UInt n (ArithmeticCircuit (Zp p))) <$$> (+)
    <$> do from @(ByteString n (ArithmeticCircuit (Zp p))) . fromConstant <$> randomIO @Integer
    <*> do from @(ByteString n (ArithmeticCircuit (Zp p))) . fromConstant <$> randomIO @Integer

leqCircuit :: Ord (Bool c) (FieldElement c) => FieldElement c -> FieldElement c -> Bool c
leqCircuit x y = x <= y

fibonacciIndexCircuit :: forall c . (Ring (FieldElement c), Eq (Bool c) (FieldElement c), Conditional (Bool c) (FieldElement c)) => Integer -> FieldElement c -> FieldElement c
fibonacciIndexCircuit nMax x = foldl @[] (\m k -> bool m (fromConstant @Integer @(FieldElement c) k) (fib k one one == x :: Bool c)) zero [1..nMax]
    where
        fib :: Integer -> FieldElement c -> FieldElement c -> FieldElement c
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

benchWitnessGeneration :: forall n p .
    KnownNat n =>
    String ->
    ArithmeticCircuit (Zp p) n ->
    Benchmark
benchWitnessGeneration desc crct =
    env (evaluate . force $ crct)
        $ bench title . nf (flip witnessGenerator []) where

    title = "Witness generation for " <> desc <> " of size " <> show (value @n)

type F = Zp BLS12_381_Scalar

main :: IO ()
main = do
    leqc <- leqCircuit @(ArithmeticCircuit F)
        <$> do fromConstant <$> randomIO @Integer
        <*> do fromConstant <$> randomIO @Integer
    fic <- fibonacciIndexCircuit @(ArithmeticCircuit F) 100
        <$> fromConstant <$> randomIO @Integer
    ac32 <- additionCircuit @32 @BLS12_381_Scalar
    ac64 <- additionCircuit @64 @BLS12_381_Scalar
    ac128 <- additionCircuit @128 @BLS12_381_Scalar
    ac256 <- additionCircuit @256 @BLS12_381_Scalar
    ac512 <- additionCircuit @512 @BLS12_381_Scalar

    ByteString hc32 <- hashCircuit @32 @BLS12_381_Scalar
    ByteString hc64 <- hashCircuit @64 @BLS12_381_Scalar
    ByteString hc128 <- hashCircuit @128 @BLS12_381_Scalar
    ByteString hc256 <- hashCircuit @256 @BLS12_381_Scalar
    ByteString hc512 <- hashCircuit @512 @BLS12_381_Scalar

    defaultMain
        [ benchWitnessGeneration "(<=) operation" . pieces @F $ leqc
        , benchWitnessGeneration "Fibonacci index" . pieces @F $ fic
        , benchWitnessGeneration "Adding ByteStrings" . pieces @F $ ac32
        , benchWitnessGeneration "Adding ByteStrings" . pieces @F $ ac64
        , benchWitnessGeneration "Adding ByteStrings" . pieces @F $ ac128
        , benchWitnessGeneration "Adding ByteStrings" . pieces @F $ ac256
        , benchWitnessGeneration "Adding ByteStrings" . pieces @F $ ac512
        , benchWitnessGeneration "Hash circuit" . pieces @F $ hc32
        , benchWitnessGeneration "Hash circuit" . pieces @F $ hc64
        , benchWitnessGeneration "Hash circuit" . pieces @F $ hc128
        , benchWitnessGeneration "Hash circuit" . pieces @F $ hc256
        , benchWitnessGeneration "Hash circuit" . pieces @F $ hc512
        ]