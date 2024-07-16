module ZkFold.Symbolic.Cardano.Types.Basic (
    FieldElement, FieldElementBits, Bool, ByteString, UInt, UTCTime,
    F,
    CtxCompilation, CtxEvaluation
    ) where

import           Prelude                                     hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit)
import qualified ZkFold.Symbolic.Data.Bool                   as Symbolic
import           ZkFold.Symbolic.Data.ByteString             (ByteString)
import           ZkFold.Symbolic.Data.UInt                   (UInt)
import           ZkFold.Symbolic.Data.UTCTime                (UTCTime)
import           ZkFold.Symbolic.Interpreter                 (Interpreter)

type FieldElement context     = context 1
type FieldElementBits context = context 256

type Bool context = Symbolic.Bool (FieldElement context)

type F = Zp BLS12_381_Scalar

type CtxCompilation = ArithmeticCircuit F
type CtxEvaluation  = Interpreter F
