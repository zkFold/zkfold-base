{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import           Control.DeepSeq                             (NFData)
import           GHC.Generics                                (U1)
import           Prelude                                     hiding (sum, (*), (+), (-), (/), (^))
import           System.Random                               (randomRIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Data.Ed25519                ()
import           ZkFold.Symbolic.Interpreter

type I = Interpreter (Zp BLS12_381_Scalar)
type A = ArithmeticCircuit (Zp BLS12_381_Scalar) U1
type PtFFA c = Point (Ed25519 c)

benchOps :: NFData a => String -> a -> (Natural-> a -> a) -> Benchmark
benchOps desc p0 op = env (fromIntegral <$> randomRIO (1 :: Integer, 3)) $ \ ~n ->
    bgroup ("Point scaling") $ [bench desc $ nf (flip op p0) n]


main :: IO ()
main = do
  defaultMain
      [ bgroup "EC operations"
        [ benchOps "FFA Interpreter" (gen :: PtFFA I) scale
        , benchOps "FFA Circuit" (gen :: PtFFA A) scale
        ]
      ]
