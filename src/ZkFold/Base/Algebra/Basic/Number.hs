{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

{-# OPTIONS_GHC -Wno-orphans  #-}

module ZkFold.Base.Algebra.Basic.Number where

import           Prelude                         hiding (Num(..), (/), (^))
import           Type.Data.Num.Unary             (Zero, Succ, (:*:))

import           ZkFold.Base.Algebra.Basic.Class

-- | Type-level natural numbers

instance Finite Zero where
    order = 0

instance Finite n => Finite (Succ n) where
    order = 1 + order @n

type N0     = Zero
type N1     = Succ N0
type N2     = Succ N1
type N4     = N2 :*: N2
type N8     = N4 :*: N2
type N16    = N8 :*: N2
type N32    = N16 :*: N2
type N64    = N32 :*: N2
type N128   = N64 :*: N2
type N256   = N128 :*: N2
type N512   = N256 :*: N2
type N1024  = N512 :*: N2
type N2048  = N1024 :*: N2
type N4096  = N2048 :*: N2
type N8192  = N4096 :*: N2
type N16384 = N8192 :*: N2
type N32768 = N16384 :*: N2