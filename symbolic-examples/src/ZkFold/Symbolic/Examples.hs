{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Examples (ExampleOutput (..), examples) where

import           Control.DeepSeq                             (NFData)
import           Data.Function                               (const, ($), (.))
import           Data.Functor.Rep                            (Rep, Representable)
import           Data.Ord                                    (Ord)
import           Data.Proxy                                  (Proxy)
import           Data.String                                 (String)
import           Data.Type.Equality                          (type (~))
import           Examples.BatchTransfer                      (exampleBatchTransfer)
import           Examples.ByteString
import           Examples.Conditional                        (exampleConditional)
import           Examples.Constant                           (exampleConst5, exampleEq5)
import           Examples.Eq                                 (exampleEq)
import           Examples.FFA
import           Examples.Fibonacci                          (exampleFibonacci)
import           Examples.LEQ                                (exampleLEQ)
import           Examples.MiMCHash                           (exampleMiMC)
import           Examples.ReverseList                        (exampleReverseList)
import           Examples.UInt
import           GHC.Generics                                (Par1, (:*:), (:.:))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compile)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit  (Var)
import           ZkFold.Symbolic.Data.ByteString             (ByteString)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators            (RegisterSize (Auto))
import ZkFold.Symbolic.Data.Input (SymbolicInput)

type A = Zp BLS12_381_Scalar
type C = ArithmeticCircuit A

data ExampleOutput where
  ExampleOutput ::
    forall i o. (Representable i, NFData (Rep i), NFData (o (Var A i))) =>
    (() -> C i o) -> ExampleOutput

exampleOutput ::
  forall i o c f.
  ( SymbolicData f
  , c ~ C i
  , Context f ~ c
  , Layout f ~ o
  , SymbolicInput (Support f)
  , Context (Support f) ~ c
  , Support (Support f) ~ Proxy c
  , Layout (Support f) ~ i
  , Representable i
  , Ord (Rep i)
  , NFData (Rep i)
  , NFData (o (Var A i))
  ) => f -> ExampleOutput
exampleOutput = ExampleOutput @i @o . const . compile

-- | TODO: Maybe there is a better place for these orphans?
instance NFData a => NFData (Par1 a)
instance (NFData (f a), NFData (g a)) => NFData ((f :*: g) a)
instance NFData (f (g a)) => NFData ((f :.: g) a)

examples :: [(String, ExampleOutput)]
examples =
  [ ("Eq", exampleOutput exampleEq)
  , ("Conditional", exampleOutput exampleConditional)
  , ("Constant.5", exampleOutput exampleConst5)
  , ("Eq.Constant.5", exampleOutput exampleEq5)
  , ("ByteString.And.32", exampleOutput $ exampleByteStringAnd @32)
  , ("ByteString.Or.64", exampleOutput $ exampleByteStringOr @64)
  , ("UInt.Mul.64.Auto", exampleOutput $ exampleUIntMul @64 @Auto)
  , ("LEQ", exampleOutput exampleLEQ)
  , ("ByteString.Extend.1.512", exampleOutput $ exampleByteStringExtend @1 @512)
  , ("ByteString.Add.512", exampleOutput $ exampleByteStringAdd @512)
  , ("UInt.StrictAdd.256.Auto", exampleOutput $ exampleUIntStrictAdd @256 @Auto)
  , ("UInt.StrictMul.512.Auto", exampleOutput $ exampleUIntStrictMul @512 @Auto)
  , ("UInt.DivMod.32.Auto", exampleOutput $ exampleUIntDivMod @32 @Auto)
  , ("Reverse.32.3000", exampleOutput $ exampleReverseList @32 @(ByteString 3000 (C _)))
  , ("Fibonacci.100", exampleOutput $ exampleFibonacci 100)
  , ("MiMCHash", exampleOutput exampleMiMC)
  , ("SHA256.32", exampleOutput $ exampleSHA @32)
  , ("FFA.Add.337", exampleOutput exampleFFAadd337)
  , ("FFA.Add.097", exampleOutput exampleFFAadd097)
  , ("FFA.Mul.337", exampleOutput exampleFFAmul337)
  , ("FFA.Mul.097", exampleOutput exampleFFAmul097)
--  , ("Ed25519.Scale", exampleOutput exampleEd25519Scale)
--  , ("PedersonCommitment", exampleOutput exampleCommitment)
  , ("BatchTransfer", exampleOutput exampleBatchTransfer)
  ]
