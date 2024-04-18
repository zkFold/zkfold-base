{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Basic.Number (KnownNat, Prime, value, type (*), type (+), type (-), type (^)) where

import           GHC.Exts     (proxy#)
import           GHC.TypeNats (KnownNat, Natural, natVal', type (*), type (+), type (-), type (^))

class KnownNat p => Prime p

value :: forall n . KnownNat n => Natural
-- argument erasure using
-- proxy# :: Proxy# (n :: Natural) :: ZeroBitType
value = natVal' (proxy# @n)
