{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Basic.Number (KnownNat, Log2, Prime, value, type (*), type (+), type (-), type (<=), type (^)) where

import           Data.Data    (Proxy (Proxy))
import           GHC.TypeNats (KnownNat, Log2, Natural, natVal, type (*), type (+), type (-), type (<=), type (^))

class KnownNat p => Prime p

value :: forall n . KnownNat n => Natural
value = natVal (Proxy @n)
