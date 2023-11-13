module ZkFold.Symbolic.Types (Symbolic, SmallField, BigField, R, I) where

import           Prelude                          (Integer)

import           ZkFold.Base.Algebra.Basic.Class  (Finite(..), Prime, FiniteField, FromConstant, ToBits)
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Symbolic.Arithmetization  (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool        (Bool)
import           ZkFold.Symbolic.Data.Conditional (Conditional)
import           ZkFold.Symbolic.Data.Eq          (Eq)
import           ZkFold.Symbolic.Data.Ord         (Ord)

type Symbolic a = (FromConstant I a, FiniteField a, ToBits a, Eq (Bool a) a, Ord (Bool a) a, Conditional (Bool a) a)

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField

type BigField = BLS12_381_Scalar

type R = ArithmeticCircuit (Zp SmallField)
type I = Integer