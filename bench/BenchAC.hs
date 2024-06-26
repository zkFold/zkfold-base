{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}

module Main where

import           Control.DeepSeq                             (force)
import           Control.Exception                           (evaluate)
import qualified Data.Map                                    as M
import           Data.Time.Clock                             (getCurrentTime)
import           Prelude                                     hiding (not, sum, (&&), (*), (+), (-), (/), (^), (||))
import           System.Random                               (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Algorithms.Hash.SHA2
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt

evalBS :: forall a n . ByteString n ArithmeticCircuit a -> Vector n a
evalBS (ByteString xs) = eval xs M.empty

evalUInt :: forall a n . UInt n ArithmeticCircuit a -> Vector (NumberOfRegisters a n) a
evalUInt (UInt xs) = eval xs M.empty


hashCircuit
    :: forall n p
    .  PrimeField (Zp p)
    => SHA2 "SHA256" ArithmeticCircuit (Zp p) n
    => IO (ByteString 256 ArithmeticCircuit (Zp p))
hashCircuit = do
    x <- randomIO
    let acX = fromConstant (x :: Integer) :: ByteString n ArithmeticCircuit (Zp p)
        h = sha2 @"SHA256" @ArithmeticCircuit acX

    evaluate . force $ h

-- | Generate random addition circuit of given size
--
additionCircuit :: forall n p. (KnownNat n, PrimeField (Zp p)) => IO (ByteString n ArithmeticCircuit (Zp p))
additionCircuit = do
    x <- randomIO
    y <- randomIO
    let acX = fromConstant (x :: Integer) :: ByteString n ArithmeticCircuit (Zp p)
        acY = fromConstant (y :: Integer) :: ByteString n ArithmeticCircuit (Zp p)

        acZ = from (from acX + from acY :: UInt n ArithmeticCircuit (Zp p))

    evaluate . force $ acZ

benchOps :: forall n p. (KnownNat n, PrimeField (Zp p)) => Benchmark
benchOps = env (additionCircuit @n @p) $ \ ~ac ->
    bench ("Adding ByteStrings of size " <> show (value @n) <> " via UInt") $ nf evalBS ac

benchHash
    :: forall n p
    .  PrimeField (Zp p)
    => SHA2 "SHA256" ArithmeticCircuit (Zp p) n
    => Benchmark
benchHash = env (hashCircuit @n @p) $ \ ~ac ->
    bench ("Calculating SHA2 512/364 of a bytestring of length " <> show (value @n)) $ nf evalBS ac

main :: IO ()
main = do
    mainSumBS
    mainHash

mainHash :: IO ()
mainHash = do
  getCurrentTime >>= print
  ByteString ac32  <- hashCircuit @32 @BLS12_381_Scalar
  getCurrentTime >>= print
  ByteString ac64  <- hashCircuit @64 @BLS12_381_Scalar
  getCurrentTime >>= print
  ByteString ac128 <- hashCircuit @128 @BLS12_381_Scalar
  getCurrentTime >>= print
  ByteString ac256 <- hashCircuit @256 @BLS12_381_Scalar
  getCurrentTime >>= print
  ByteString ac512 <- hashCircuit @512 @BLS12_381_Scalar
  getCurrentTime >>= print

  putStrLn "Sizes"

  print $ acSizeM ac32
  getCurrentTime >>= print
  print $ acSizeM ac64
  getCurrentTime >>= print
  print $ acSizeM ac128
  getCurrentTime >>= print
  print $ acSizeM ac256
  getCurrentTime >>= print
  print $ acSizeM ac512
  getCurrentTime >>= print

  putStrLn "Evaluation"

  print $ exec ac32
  getCurrentTime >>= print
  print $ exec ac64
  getCurrentTime >>= print
  print $ exec ac128
  getCurrentTime >>= print
  print $ exec ac256
  getCurrentTime >>= print
  print $ exec ac512
  getCurrentTime >>= print

  defaultMain
      [ benchHash @32 @BLS12_381_Scalar
      , benchHash @64 @BLS12_381_Scalar
      , benchHash @128 @BLS12_381_Scalar
      , benchHash @256 @BLS12_381_Scalar
      , benchHash @512 @BLS12_381_Scalar
      ]

mainSumBS :: IO ()
mainSumBS = do
  ByteString ac32 <- additionCircuit @32 @BLS12_381_Scalar
  ByteString ac64 <- additionCircuit @64 @BLS12_381_Scalar
  ByteString ac128 <- additionCircuit @128 @BLS12_381_Scalar
  ByteString ac256 <- additionCircuit @256 @BLS12_381_Scalar
  ByteString ac512 <- additionCircuit @512 @BLS12_381_Scalar

  print $ acSizeM ac32
  print $ acSizeM ac64
  print $ acSizeM ac128
  print $ acSizeM ac256
  print $ acSizeM ac512

  defaultMain
      [ benchOps @32 @BLS12_381_Scalar
      , benchOps @64 @BLS12_381_Scalar
      , benchOps @128 @BLS12_381_Scalar
      , benchOps @256 @BLS12_381_Scalar
      , benchOps @512 @BLS12_381_Scalar
      ]

