module Main where

import           Control.DeepSeq                 (NFData, force)
import           Control.Monad                   (return)
import           Data.ByteString.Lazy            (ByteString)
import           Data.Function                   (const, ($))
import           Data.Functor.Rep                (Representable (..))
import           Data.Semigroup                  ((<>))
import           Data.String                     (String, fromString)
import           System.IO                       (IO)
import           Test.Tasty.Bench
import           Test.Tasty.Golden               (goldenVsString)
import           Text.Show                       (show)

import           ZkFold.Base.Algebra.Basic.Class (zero)
import           ZkFold.Symbolic.Class           (Arithmetic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Examples

metrics :: String -> ArithmeticCircuit a p i o -> ByteString
metrics name circuit =
  fromString name
  <> "\nNumber of constraints: " <> fromString (show $ acSizeN circuit)
  <> "\nNumber of variables: " <> fromString (show $ acSizeM circuit)
  <> "\nNumber of range lookups: " <> fromString (show $ acSizeR circuit)


benchmark ::
  (Arithmetic a, NFData (o (Var a i)), NFData (Rep i), Representable i) =>
  String -> (() -> ArithmeticCircuit a p i o) -> Benchmark
benchmark name circuit = bgroup name
  [ bench "compilation" $ nf circuit ()
  , env (return $ force $ circuit ()) $ \c ->
    let
        input = tabulate (const zero)
        path = "stats/" <> name
     in bgroup "on compilation"
          [ bench "evaluation" $ nf (witnessGenerator c) input
          , goldenVsString "# of constraints" path $ return (metrics name c)
          ]
  ]

main :: IO ()
main = defaultMain [ benchmark n c | (n, ExampleOutput c) <- examples ]
