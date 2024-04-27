{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Basic.Number (KnownNat, Prime, value, type (*), type (+), type (-), type (^)) where

import           Data.Data    (Proxy (Proxy))
import           GHC.TypeNats (KnownNat, Natural, natVal, type (*), type (+), type (-), type (^))
import           ZkFold.Base.Algebra.Basic.Prime (Prime)

value :: forall n . KnownNat n => Natural
value = natVal (Proxy @n)
