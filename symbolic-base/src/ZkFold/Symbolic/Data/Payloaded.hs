{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Payloaded where

import           Data.Function                    (const, ($), (.))
import           Data.Proxy                       (Proxy (..))
import           Data.Tuple                       (snd)
import           GHC.Generics                     (U1 (..))

import           ZkFold.Base.Control.HApplicative (hunit)
import           ZkFold.Symbolic.Class            (Symbolic (..))
import           ZkFold.Symbolic.Data.Bool        (true)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Input       (SymbolicInput (..))

newtype Payloaded f c = Payloaded { runPayloaded :: f (WitnessField c) }

instance (Symbolic c, PayloadFunctor f) => SymbolicData (Payloaded f c) where
  type Context (Payloaded f c) = c
  type Support (Payloaded f c) = Proxy c
  type Layout (Payloaded f c) = U1
  type Payload (Payloaded f c) = f

  arithmetize _ _ = hunit
  payload = const . runPayloaded
  restore = Payloaded . snd . ($ Proxy)

instance (Symbolic c, PayloadFunctor f) => SymbolicInput (Payloaded f c) where
  isValid = const true
