module ZkFold.Symbolic.Cardano.Types.Basic where

import           Prelude                                     hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit)
import qualified ZkFold.Symbolic.Data.Bool                   as Symbolic
import qualified ZkFold.Symbolic.Data.ByteString             as Symbolic
import qualified ZkFold.Symbolic.Data.UInt                   as Symbolic
import qualified ZkFold.Symbolic.Data.UTCTime                as Symbolic

type F = Zp BLS12_381_Scalar

type FieldElement context     = context 1 F
type FieldElementBits context = context 256 F

type Bool context = Symbolic.Bool (FieldElement context)

type UInt n context = Symbolic.UInt n context F

type UTCTime context = Symbolic.UTCTime context F

type ByteString n context = Symbolic.ByteString n context F

type CtxCompilation = ArithmeticCircuit
type CtxEvaluation  = Vector