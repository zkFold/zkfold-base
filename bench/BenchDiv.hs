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
import           Prelude                                     hiding (not, sum, (&&), (*), (+), (-), (/), (^), (||), divMod)
import           System.Random                               (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.Combinators

evalUInt :: forall a n . UInt n ArithmeticCircuit a -> Vector (NumberOfRegisters a n) a
evalUInt (UInt xs) = eval xs M.empty

-- | Generate random addition circuit of given size
--
divisionCircuit 
    :: forall n p r
    .  KnownNat n
    => PrimeField (Zp p)
    => r ~ NumberOfRegisters (Zp p) n
    => KnownNat r
    => KnownNat (r - 1)
    => KnownNat (r + r)
    => 1 + (r - 1) ~ r
    => 1 <= r
    => IO (UInt n ArithmeticCircuit (Zp p), UInt n ArithmeticCircuit (Zp p))
divisionCircuit = do
    x <- randomIO
    y <- randomIO
    let acX = fromConstant (x :: Integer) :: UInt n ArithmeticCircuit (Zp p)
        acY = fromConstant (y :: Integer) :: UInt n ArithmeticCircuit (Zp p)

        acZ = acX `divMod` acY 

    evaluate . force $ acZ

benchOps
    :: forall n p r
    .  KnownNat n
    => PrimeField (Zp p)
    => r ~ NumberOfRegisters (Zp p) n
    => KnownNat r
    => KnownNat (r - 1)
    => KnownNat (r + r)
    => 1 + (r - 1) ~ r
    => 1 <= r
    => Benchmark
benchOps = env (divisionCircuit @n @p) $ \ ~ac ->
    bench ("Dividing UInts of size " <> show (value @n)) $ nf (\(a, b) -> (evalUInt a, evalUInt b)) ac

main :: IO ()
main = do
  getCurrentTime >>= print
  (UInt ac32q, UInt ac32r)  <- divisionCircuit @32 @BLS12_381_Scalar
  getCurrentTime >>= print
  (UInt ac64q,  UInt ac64r)  <- divisionCircuit @64 @BLS12_381_Scalar
  getCurrentTime >>= print
  (UInt ac128q, UInt ac128r) <- divisionCircuit @128 @BLS12_381_Scalar
  getCurrentTime >>= print
--  (UInt ac256q, UInt ac256r) <- divisionCircuit @256 @BLS12_381_Scalar
--  getCurrentTime >>= print
--  (UInt ac512q, UInt ac512r) <- divisionCircuit @512 @BLS12_381_Scalar
--  getCurrentTime >>= print

  putStrLn "Sizes"

  print $ (acSizeM ac32q, acSizeM ac32r)
  getCurrentTime >>= print
  print $ (acSizeM ac64q, acSizeM ac64r)
  getCurrentTime >>= print
  print $ (acSizeM ac128q, acSizeM ac128r)
  getCurrentTime >>= print
--  print $ (acSizeM ac256q, acSizeM ac256r)
--  getCurrentTime >>= print
--  print $ (acSizeM ac512q, acSizeM ac512r)
--  getCurrentTime >>= print

  putStrLn "Evaluation"

  print $ (exec ac32q, exec ac32r)
  getCurrentTime >>= print
  print $ (exec ac64q, exec ac64r)
  getCurrentTime >>= print
  print $ (exec ac128q, exec ac128r)
  getCurrentTime >>= print
--  print $ (exec ac256q, exec ac256r)
--  getCurrentTime >>= print
--  print $ (exec ac512q, exec ac512r)
--  getCurrentTime >>= print

  defaultMain
      [ benchOps @32 @BLS12_381_Scalar
      , benchOps @64 @BLS12_381_Scalar
      , benchOps @128 @BLS12_381_Scalar
--      , benchOps @256 @BLS12_381_Scalar
--      , benchOps @512 @BLS12_381_Scalar
      ]

