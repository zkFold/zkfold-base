module Main where

import           Control.DeepSeq                 (NFData, force)
import           Control.Monad                   (return)
import           Data.ByteString.Lazy            (ByteString)
import           Data.Function                   (($))
import           Data.Map                        (Map, fromAscList)
import           Data.Semigroup                  ((<>))
import           Data.String                     (String, fromString)
import           Numeric.Natural                 (Natural)
import           System.IO                       (IO)
import           Test.Tasty.Bench
import           Test.Tasty.Golden               (goldenVsString)
import           Text.Show                       (show)

import           ZkFold.Base.Algebra.Basic.Class (AdditiveMonoid, zero)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Examples

inputMap :: AdditiveMonoid a => ArithmeticCircuit a o -> Map Natural a
inputMap circuit = fromAscList [ (i, zero) | i <- acInput circuit ]

metrics :: String -> ArithmeticCircuit a o -> ByteString
metrics name circuit =
  fromString name
  <> "\nNumber of constraints: " <> fromString (show $ acSizeN circuit)
  <> "\nNumber of variables: " <> fromString (show $ acSizeM circuit)
  <> "\nNumber of range lookups: " <> fromString (show $ acSizeR circuit)

benchmark ::
  (NFData a, AdditiveMonoid a, NFData (o Natural)) =>
  String -> (() -> ArithmeticCircuit a o) -> Benchmark
benchmark name circuit = bgroup name
  [ bench "compilation" $ nf circuit ()
  , env (return $ force $ circuit ()) $ \c ->
    let input = inputMap c
        path = "stats/" <> name
     in bgroup "on compilation"
          [ bench "evaluation" $ nf (witnessGenerator c) input
          , goldenVsString "# of constraints" path $ return (metrics name c)
          ]
  ]

main :: IO ()
main = defaultMain [ benchmark n c | (n, ExampleOutput c) <- examples ]
