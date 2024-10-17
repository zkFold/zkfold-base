{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module ZkFold.UPLC.BuiltinType where

import           GHC.TypeNats    (type (+))
import           Numeric.Natural (Natural)

data Fin (n :: Natural) where
  Z :: Fin (n + 1)
  S :: Fin n -> Fin (n + 1)

data BuiltinType (n :: Natural)
  = BTVar (Fin n)
  | BTInteger
  | BTByteString
  | BTString
  | BTBool
  | BTUnit
  | BTData
  | BTList (BuiltinType n)
  | BTPair (BuiltinType n) (BuiltinType n)
  | BTBLSG1 -- ^ Batch 4
  | BTBLSG2 -- ^ Batch 4
  | BTBLSMLResult -- ^ Batch 4
