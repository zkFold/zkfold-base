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
import           Data.Time.Clock                             (getCurrentTime)
import           Prelude                                     hiding (divMod, not, sum, (&&), (*), (+), (-), (/), (^),
                                                              (||))
import           System.Random                               (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt

evalUInt :: forall a n r . UInt n r (ArithmeticCircuit a)-> Vector (NumberOfRegisters a n r) a
evalUInt (UInt v) = exec v

-- | Generate random addition circuit of given size
--
divisionCircuit
    :: forall n p r rs
    .  KnownNat n
    => KnownRegisterSize r
    => rs ~ NumberOfRegisters (Zp p) n r
    => KnownNat rs
    => KnownNat (rs - 1)
    => KnownNat (rs + rs)
    => PrimeField (Zp p)
    => IO (UInt n r (ArithmeticCircuit (Zp p)), UInt n r (ArithmeticCircuit (Zp p)))
divisionCircuit = do
    x <- randomIO
    y <- randomIO
    let acX = fromConstant (x :: Integer) :: UInt n r (ArithmeticCircuit (Zp p))
        acY = fromConstant (y :: Integer) :: UInt n r (ArithmeticCircuit (Zp p))

        acZ = acX `divMod` acY

    evaluate . force $ acZ

benchOps
    :: forall n p (r :: RegisterSize) rs
    .  KnownNat n
    => PrimeField (Zp p)
    => KnownRegisterSize r
    => rs ~ NumberOfRegisters (Zp p) n r
    => KnownNat rs
    => KnownNat (rs - 1)
    => KnownNat (rs + rs)
    => Benchmark
benchOps = env (divisionCircuit @n @p @r) $ \ ~ac ->
    bench ("Dividing UInts of size " <> show (value @n)) $ nf (\(a, b) -> (evalUInt a, evalUInt b)) ac

main :: IO ()
main = do
  getCurrentTime >>= print
  (UInt ac32q, UInt ac32r)  <- divisionCircuit @32 @BLS12_381_Scalar @Auto
  getCurrentTime >>= print
  (UInt ac64q,  UInt ac64r)  <- divisionCircuit @64 @BLS12_381_Scalar @Auto
  getCurrentTime >>= print
  (UInt ac128q, UInt ac128r) <- divisionCircuit @128 @BLS12_381_Scalar @Auto
  getCurrentTime >>= print

  putStrLn "Sizes"

  print $ (acSizeM ac32q, acSizeM ac32r)
  getCurrentTime >>= print
  print $ (acSizeM ac64q, acSizeM ac64r)
  getCurrentTime >>= print
  print $ (acSizeM ac128q, acSizeM ac128r)
  getCurrentTime >>= print

  putStrLn "Evaluation"

  print $ (exec ac32q, exec ac32r)
  getCurrentTime >>= print
  print $ (exec ac64q, exec ac64r)
  getCurrentTime >>= print
  print $ (exec ac128q, exec ac128r)
  getCurrentTime >>= print

  defaultMain
      [ benchOps @32 @BLS12_381_Scalar @Auto
      , benchOps @64 @BLS12_381_Scalar @Auto
      , benchOps @128 @BLS12_381_Scalar @Auto
      ]

