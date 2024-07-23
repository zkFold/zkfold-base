{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Examples (ExampleOutput (..), examples) where

import           Control.DeepSeq                             (NFData)
import           Data.Function                               (const, ($), (.))
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

type A = Zp BLS12_381_Scalar
type C = ArithmeticCircuit A

data ExampleOutput where
  ExampleOutput :: forall o. NFData (o Natural) => (() -> C o) -> ExampleOutput

exampleOutput ::
  forall n f.
  ( SymbolicData C f
  , SymbolicData C (Support C f)
  , KnownNat (TypeSize C (Support C f))
  , TypeSize C f ~ n
  , Support C (Support C f) ~ ()
  ) => f -> ExampleOutput
exampleOutput = ExampleOutput @(Vector n) . const . compile @A

examples :: [(String, ExampleOutput)]
examples =
  [ ("Eq", exampleOutput $ exampleEq @C)
  , ("Conditional", exampleOutput $ exampleConditional @C)
  , ("ByteString.And.32", exampleOutput @32 $ exampleByteStringAnd @C)
  , ("ByteString.Or.64", exampleOutput @64 $ exampleByteStringOr @C)
  , ("UInt.Mul.64.Auto", exampleOutput @1 $ exampleUIntMul @64 @Auto @C)
  , ("LEQ", exampleOutput $ exampleLEQ @C)
  , ("ByteString.Extend.1.512", exampleOutput @512 $ exampleByteStringExtend @C @1)
  , ("ByteString.Add.512", exampleOutput @512 $ exampleByteStringAdd @C)
  , ("UInt.StrictAdd.256.Auto", exampleOutput @3 $ exampleUIntStrictAdd @256 @Auto @C)
  , ("UInt.StrictMul.512.Auto", exampleOutput @5 $ exampleUIntStrictMul @512 @Auto @C)
  , ("UInt.DivMod.32.Auto", exampleOutput @2 $ exampleUIntDivMod @32 @Auto @C)
  , ("Reverse.32.3000", exampleOutput $ exampleReverseList @32 @(ByteString 3000 C))
  , ("Fibonacci.100", exampleOutput $ exampleFibonacci @C 100)
  , ("MiMCHash", exampleOutput $ exampleMiMC @C)
  , ("SHA256.32", exampleOutput $ exampleSHA @C @32)
  , ("FFA.Add.337", exampleOutput $ exampleFFAadd337 @C)
  , ("FFA.Add.097", exampleOutput $ exampleFFAadd097 @C)
  , ("FFA.Mul.337", exampleOutput $ exampleFFAmul337 @C)
  , ("FFA.Mul.097", exampleOutput $ exampleFFAmul097 @C)
  , ("BatchTransfer", exampleOutput $ exampleBatchTransfer @C)
  ]
