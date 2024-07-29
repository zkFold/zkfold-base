{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import           Control.Applicative                            ((<*>))
import           Data.Aeson                                     (ToJSON)
import           Data.Foldable                                  (foldl)
import           Data.Function                                  (($), (.))
import           Data.Functor                                   ((<$>))
import           Data.List                                      (reverse)
import           Data.String                                    (String)
import           GHC.Integer                                    (Integer)
import           System.IO                                      (IO)
import           System.Random                                  (randomIO)
import           Test.Tasty.Bench                               (Benchmark, bench, defaultMain, nfIO)

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
fibonacciIndexCircuit nMax x = foldl (\m k -> bool m (fromConstant @Integer @(FieldElement c) k) (fib k one one == x :: Bool c)) zero [1..nMax]
    where
        fib :: Integer -> FieldElement c -> FieldElement c -> FieldElement c
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

reverseListCircuit :: forall t n . Vector n t -> Vector n t
reverseListCircuit = unsafeToVector . reverse . fromVector

benchFileCompilation :: forall a f .
   (ToJSON a, Arithmetizable a f, KnownNat (InputSize a f)) =>
   String -> String -> f -> Benchmark
benchFileCompilation title fp =
    bench title . nfIO . writeFileJSON fp . optimize . solder @a

type F = Zp BLS12_381_Scalar

main :: IO ()
main = do
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
        [ benchFileCompilation @F "(<=) operation" "compiled_scripts/leq.json" $ leqCircuit @(ArithmeticCircuit F)
        , benchFileCompilation @F "Reversing a list" "compiled_scripts/reverse_list_32.json"$  reverseListCircuit @(ArithmeticCircuit F 1) @32
        , benchFileCompilation @F "Fibonacci index" "compiled_scripts/fibonacci_index_100.json" $ fibonacciIndexCircuit @(ArithmeticCircuit F) 100
        , benchFileCompilation @F "MIMC hash" "compiled_scripts/mimc_hash_2.json" $ mimcHash2 @F @(ArithmeticCircuit F 1) mimcConstants zero
        , benchFileCompilation @F "Adding ByteStrings" "compiled_scripts/add_bytestrings_32.json" ac32
        , benchFileCompilation @F "Adding ByteStrings" "compiled_scripts/add_bytestrings_64.json" ac64
        , benchFileCompilation @F "Adding ByteStrings" "compiled_scripts/add_bytestrings_128.json" ac128
        , benchFileCompilation @F "Adding ByteStrings" "compiled_scripts/add_bytestrings_256.json" ac256
        , benchFileCompilation @F "Adding ByteStrings" "compiled_scripts/add_bytestrings_512.json" ac512
        , benchFileCompilation @F "Hash circuit" "compiled_scripts/hash_circuit_32.json" hc32
        , benchFileCompilation @F "Hash circuit" "compiled_scripts/hash_circuit_64.json" hc64
        , benchFileCompilation @F "Hash circuit" "compiled_scripts/hash_circuit_128.json" hc128
        , benchFileCompilation @F "Hash circuit" "compiled_scripts/hash_circuit_256.json" hc256
        , benchFileCompilation @F "Hash circuit" "compiled_scripts/hash_circuit_512.json" hc512
        ]
