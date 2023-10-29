module ZkFold.Symbolic.Types (Symbolic, SmallField, R, I) where

import           Prelude                          (Integer)

import           ZkFold.Base.Algebra.Basic.Class  (Finite(..), Prime, FiniteField, FromConstant, ToBits)
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
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

type R = ArithmeticCircuit (Zp SmallField)
type I = Integer

data BLS12_381_Scalar
instance Finite BLS12_381_Scalar where
    order = 52435875175126190479447740508185965837690552500527637822603658699938581184513
instance Prime BLS12_381_Scalar