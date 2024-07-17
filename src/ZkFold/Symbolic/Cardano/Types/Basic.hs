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
import qualified ZkFold.Symbolic.Data.ByteString             as Symbolic
import qualified ZkFold.Symbolic.Data.FieldElement           as Symbolic
import qualified ZkFold.Symbolic.Data.UInt                   as Symbolic
import qualified ZkFold.Symbolic.Data.UTCTime                as Symbolic

type F = Zp BLS12_381_Scalar

type FieldElement context     = Symbolic.FieldElement context F
type FieldElementBits context = context 256 F

type Bool context = Symbolic.Bool (context 1 F)

type F = Zp BLS12_381_Scalar

type CtxCompilation = ArithmeticCircuit F
type CtxEvaluation  = Interpreter F
