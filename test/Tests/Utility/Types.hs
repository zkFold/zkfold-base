module Tests.Utility.Types (SmallField, R, I) where

import           Prelude                                     (Integer)

import           ZkFold.Crypto.Algebra.Basic.Class           (Finite(..), Prime)
import           ZkFold.Crypto.Algebra.Basic.Field           (Zp)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (R1CS)

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField

type R = R1CS (Zp SmallField)
type I = Integer