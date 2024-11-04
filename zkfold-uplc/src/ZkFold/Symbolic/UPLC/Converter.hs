{-# LANGUAGE ExistentialQuantification #-}

module ZkFold.Symbolic.UPLC.Converter (ScriptType (..), SomeCircuit (..), convert) where

import           Data.Function                               (($))
import           GHC.Generics                                (Par1)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compile)
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.Maybe                  (isJust)
import           ZkFold.Symbolic.UPLC.Data                   (Data)
import           ZkFold.Symbolic.UPLC.Evaluation             (ExValue (ExValue), MaybeValue (..), Sym, eval)
import           ZkFold.UPLC.Term                            (Term)

data ScriptType = SpendingV1 | OtherV1 | V3
data SomeCircuit = forall i. SomeCircuit (ArithmeticCircuit (Zp BLS12_381_Scalar) i Par1)

convert :: Term -> ScriptType -> SomeCircuit
convert t SpendingV1 = SomeCircuit $ compile (spendingContract t)
convert t OtherV1    = SomeCircuit $ compile (otherContract t)
convert t V3         = SomeCircuit $ compile (contractV3 t)

type DatumCtx c = Data c
type RedeemerCtx c = Data c
type ScriptCtx c = Data c

spendingContract :: Sym c => Term -> DatumCtx c -> RedeemerCtx c -> ScriptCtx c -> Bool c
spendingContract t d r s = contract t [ExValue d, ExValue r, ExValue s]

otherContract :: Sym c => Term -> RedeemerCtx c -> ScriptCtx c -> Bool c
otherContract t r s = contract t [ExValue r, ExValue s]

contractV3 :: Sym c => Term -> ScriptCtx c -> Bool c
contractV3 t s = contract t [ExValue s]

contract :: Sym c => Term -> [ExValue c] -> Bool c
contract t s = case eval t s of
  MaybeValue v -> isJust v
