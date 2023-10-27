module Tests.Utility.Types (Symbolic, SmallField, R, I) where

import           Prelude                                   (Integer)

import           ZkFold.Base.Algebra.Basic.Class           (Finite(..), Prime, FiniteField, FromConstant, ToBits)
import           ZkFold.Base.Algebra.Basic.Field           (Zp)
import           ZkFold.Base.Data.Bool                     (Bool)
import           ZkFold.Base.Data.Conditional              (Conditional)
import           ZkFold.Base.Data.Eq                       (Eq)
import           ZkFold.Base.Data.Ord                      (Ord)
import           ZkFold.Base.Protocol.Arithmetization.R1CS (ArithmeticCircuit)

type Symbolic a = (FromConstant I a, FiniteField a, ToBits a, Eq (Bool a) a, Ord (Bool a) a, Conditional (Bool a) a)

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField

type R = ArithmeticCircuit (Zp SmallField)
type I = Integer