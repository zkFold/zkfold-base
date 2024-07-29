{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications             #-}

{-# OPTIONS_GHC -freduction-depth=0 #-}

module Main where

import           Control.DeepSeq                                (force)
import           Control.Exception                              (evaluate)
import           Data.Aeson                                     (ToJSON)
import qualified Data.Map                                       as M
import           Data.Time                                      (getCurrentTime)
import           Prelude                                        hiding (Bool (..), Eq (..), Ord (..), not, sum, (&&),
                                                                 (*), (+), (-), (/), (<=), (^), (||))
import           System.Random                                  (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector                        hiding (reverse)
import           ZkFold.Prelude
import           ZkFold.Symbolic.Algorithms.Hash.MiMC
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants
import           ZkFold.Symbolic.Algorithms.Hash.SHA2
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.UInt

evalBS :: forall a n . ByteString n (ArithmeticCircuit a) -> Vector n a
evalBS (ByteString xs) = eval xs M.empty

evalUInt :: forall a n r . UInt n r (ArithmeticCircuit a) -> Vector (NumberOfRegisters a n r) a
evalUInt (UInt xs) = eval xs M.empty

hashCircuit :: forall n p .
   PrimeField (Zp p) =>
   SHA2 "SHA256" (ArithmeticCircuit (Zp p)) n =>
   IO (ByteString 256 (ArithmeticCircuit (Zp p)))
hashCircuit = sha2 @"SHA256" @(ArithmeticCircuit (Zp p)) @n . fromConstant <$> randomIO @Integer

-- | Generate random addition circuit of given size
additionCircuit :: forall n p r .
    (KnownNat n, PrimeField (Zp p), KnownRegisterSize r) =>
    IO (ByteString n (ArithmeticCircuit (Zp p)))
additionCircuit = from @(UInt n r (ArithmeticCircuit (Zp p))) <$$> (+)
    <$> do from @(ByteString n (ArithmeticCircuit (Zp p))) . fromConstant <$> randomIO @Integer
    <*> do from @(ByteString n (ArithmeticCircuit (Zp p))) . fromConstant <$> randomIO @Integer

benchCircuit :: forall n p .
    KnownNat n =>
    String ->
    IO (ByteString n (ArithmeticCircuit (Zp p))) ->
    Benchmark
benchCircuit desc crct = env (crct >>= evaluate . force) $ bench title . nf evalBS where

    title = "Calculating " <> desc <> " of size " <> show (value @n)

printCircuitSize :: forall p n .
    PrimeField (Zp p) =>
    IO (ByteString n (ArithmeticCircuit (Zp p))) -> IO ()
printCircuitSize crct = crct
    >>= evaluate . force
    >>= print . acSizeM . toFieldElements @(ArithmeticCircuit (Zp p))

benchCompilation :: forall a f .
   (ToJSON a, Arithmetizable a f, KnownNat (InputSize a f)) =>
   String -> FilePath -> f -> Benchmark
benchCompilation title fp =
    bench title . nfIO . writeFileJSON fp . optimize . solder @a

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
      [ benchCircuit "SHA2 512/364" $ hashCircuit @32 @BLS12_381_Scalar
      , benchCircuit "SHA2 512/364" $ hashCircuit @64 @BLS12_381_Scalar
      , benchCircuit "SHA2 512/364" $ hashCircuit @128 @BLS12_381_Scalar
      , benchCircuit "SHA2 512/364" $ hashCircuit @256 @BLS12_381_Scalar
      , benchCircuit "SHA2 512/364" $ hashCircuit @512 @BLS12_381_Scalar
      ]

mainSumBS :: IO ()
mainSumBS = do

  printCircuitSize $ additionCircuit @32 @BLS12_381_Scalar @Auto
  printCircuitSize $ additionCircuit @64 @BLS12_381_Scalar @Auto
  printCircuitSize $ additionCircuit @128 @BLS12_381_Scalar @Auto
  printCircuitSize $ additionCircuit @256 @BLS12_381_Scalar @Auto
  printCircuitSize $ additionCircuit @512 @BLS12_381_Scalar @Auto

  defaultMain
      [ benchCircuit "Adding ByteStrings" $ additionCircuit @32 @BLS12_381_Scalar @Auto
      , benchCircuit "Adding ByteStrings" $ additionCircuit @64 @BLS12_381_Scalar @Auto
      , benchCircuit "Adding ByteStrings" $ additionCircuit @128 @BLS12_381_Scalar @Auto
      , benchCircuit "Adding ByteStrings" $ additionCircuit @256 @BLS12_381_Scalar @Auto
      , benchCircuit "Adding ByteStrings" $ additionCircuit @512 @BLS12_381_Scalar @Auto
      ]
