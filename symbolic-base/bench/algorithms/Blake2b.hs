{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

import qualified Data.ByteString.Internal                    as BI
import           Prelude                                     hiding (sum, (*), (+), (-), (/), (^))
import           System.Random                               (genByteString, initStdGen)
import           Test.Tasty.Bench                            (Benchmark, bench, bgroup, defaultMain, nf)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (fromConstant), ToConstant (..))
import           ZkFold.Base.Algebra.Basic.Field             
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b     (blake2b_224)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Data.ByteString             (ByteString)
import           ZkFold.Symbolic.Interpreter                 (Interpreter)

inputGen :: Int -> IO BI.ByteString
inputGen size = do
    g <- initStdGen
    let (b, _) = genByteString size g
    pure b

sizes :: [Int]
sizes = [1, 2, 3, 4, 8, 12, 16, 20, 28, 32, 64, 100, 128, 256, 512, 4096]

bytes :: forall len c . (Symbolic c
   , ToConstant (ByteString 224 c)
   , Const (ByteString 224 c) ~ Natural) =>
   (ByteString (len * 8) c -> ByteString 224 c) -> BI.ByteString -> Natural
bytes f = toConstant @(ByteString 224 c) . f . fromConstant @BI.ByteString @(ByteString (len * 8) c)

ops :: forall c . (Symbolic c
   , ToConstant (ByteString 224 c)
   , Const (ByteString 224 c) ~ Natural) =>
   [(String, BI.ByteString -> Natural)]
ops =
    [ ("Small hash ", bytes $ blake2b_224 @1 @c)
    , ("Small hash ", bytes $ blake2b_224 @2 @c)
    , ("Small hash ", bytes $ blake2b_224 @3 @c)
    , ("Small hash ", bytes $ blake2b_224 @4 @c)
    ---
    , ("Medium hash ", bytes $ blake2b_224 @8 @c)
    , ("Medium hash ", bytes $ blake2b_224 @12 @c)
    , ("Medium hash ", bytes $ blake2b_224 @16 @c)
    , ("Medium hash ", bytes $ blake2b_224 @20 @c)
    ---
    , ("Large hash ", bytes $ blake2b_224 @28 @c)
    , ("Large hash ", bytes $ blake2b_224 @32 @c)
    , ("Large hash ", bytes $ blake2b_224 @64 @c)
        ---
    , ("Large hash ", bytes $ blake2b_224 @100 @c)
    , ("Large hash ", bytes $ blake2b_224 @128 @c)
    , ("Large hash ", bytes $ blake2b_224 @256 @c)
            ---
    , ("Large hash ", bytes $ blake2b_224 @512 @c)
    , ("Large hash ", bytes $ blake2b_224 @4096 @c)
    ]

benchOps :: [(BI.ByteString, (String, BI.ByteString -> Natural))] -> [Benchmark]
benchOps testOps = flip fmap testOps $ \(input, (desc, op)) -> bench desc $ nf op input

main :: IO ()
main = do
  inputs <- mapM inputGen sizes
  let benchs = zip inputs $ ops @(Interpreter (Zp BLS12_381_Scalar))
  defaultMain
    [ bgroup "Field with roots of unity" $ benchOps benchs
    ]
