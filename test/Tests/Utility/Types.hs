module Tests.Utility.Types (Symbolic, SmallField, R, I) where

import           Prelude                                   (Integer)

import           ZkFold.Base.Algebra.Basic.Class           (Finite(..), Prime, FiniteField, FromConstant, ToBits)
import           ZkFold.Base.Algebra.Basic.Field           (Zp)
import           ZkFold.Base.Data.Bool                     (Bool)
import           ZkFold.Base.Data.Conditional              (GeneralizedConditional)
import           ZkFold.Base.Data.Eq                       (GeneralizedEq)
import           ZkFold.Base.Data.Ord                      (GeneralizedOrd)
import           ZkFold.Base.Protocol.Arithmetization.R1CS (R1CS)

type Symbolic a = (FromConstant I a, FiniteField a, ToBits a, GeneralizedEq (Bool a) a, GeneralizedOrd (Bool a) a, GeneralizedConditional (Bool a) a)

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField

type R = R1CS (Zp SmallField)
type I = Integer