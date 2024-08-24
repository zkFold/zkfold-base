{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Examples (ExampleOutput (..), examples) where

import           Control.DeepSeq                             (NFData)
import           Data.Function                               (const, ($), (.))
import           Data.Proxy                                  (Proxy)
import           Data.String                                 (String)
import           Data.Type.Equality                          (type (~))
import           Examples.BatchTransfer                      (exampleBatchTransfer)
import           Examples.ByteString
import           Examples.Conditional                        (exampleConditional)
import           Examples.Eq                                 (exampleEq)
import           Examples.FFA
import           Examples.Fibonacci                          (exampleFibonacci)
import           Examples.LEQ                                (exampleLEQ)
import           Examples.MiMCHash                           (exampleMiMC)
import           Examples.ReverseList                        (exampleReverseList)
import           Examples.UInt

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number            (KnownNat, Natural)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compile)
import           ZkFold.Symbolic.Data.ByteString             (ByteString)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators            (RegisterSize (Auto))

type C = ArithmeticCircuit (Zp BLS12_381_Scalar)

data ExampleOutput where
  ExampleOutput :: forall o. NFData (o Natural) => (() -> C o) -> ExampleOutput

exampleOutput ::
  forall n f.
  ( SymbolicData f
  , Context f ~ C
  , TypeSize f ~ n
  , SymbolicData (Support f)
  , Context (Support f) ~ C
  , Support (Support f) ~ Proxy C
  , KnownNat (TypeSize (Support f))
  ) => f -> ExampleOutput
exampleOutput = ExampleOutput @(Vector n) . const . compile

examples :: [(String, ExampleOutput)]
examples =
  [ ("Eq", exampleOutput exampleEq)
  , ("Conditional", exampleOutput exampleConditional)
  , ("ByteString.And.32", exampleOutput $ exampleByteStringAnd @32)
  , ("ByteString.Or.64", exampleOutput $ exampleByteStringOr @64)
  , ("UInt.Mul.64.Auto", exampleOutput $ exampleUIntMul @64 @Auto)
  , ("LEQ", exampleOutput exampleLEQ)
  , ("ByteString.Extend.1.512", exampleOutput $ exampleByteStringExtend @1 @512)
  , ("ByteString.Add.512", exampleOutput $ exampleByteStringAdd @512)
  , ("UInt.StrictAdd.256.Auto", exampleOutput $ exampleUIntStrictAdd @256 @Auto)
  , ("UInt.StrictMul.512.Auto", exampleOutput $ exampleUIntStrictMul @512 @Auto)
  , ("UInt.DivMod.32.Auto", exampleOutput $ exampleUIntDivMod @32 @Auto)
  , ("Reverse.32.3000", exampleOutput $ exampleReverseList @32 @(ByteString 3000 C))
  , ("Fibonacci.100", exampleOutput $ exampleFibonacci 100)
  , ("MiMCHash", exampleOutput exampleMiMC)
  , ("SHA256.32", exampleOutput $ exampleSHA @32)
  , ("FFA.Add.337", exampleOutput exampleFFAadd337)
  , ("FFA.Add.097", exampleOutput exampleFFAadd097)
  , ("FFA.Mul.337", exampleOutput exampleFFAmul337)
  , ("FFA.Mul.097", exampleOutput exampleFFAmul097)
  , ("BatchTransfer", exampleOutput exampleBatchTransfer)
  ]
