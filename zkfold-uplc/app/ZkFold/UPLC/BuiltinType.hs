module ZkFold.UPLC.BuiltinType where

data BuiltinType
  = BTInteger
  | BTByteString
  | BTString
  | BTBool
  | BTUnit
  | BTData
  | BTList BuiltinType
  | BTPair BuiltinType BuiltinType
  | BTBLSG1 -- ^ Batch 4
  | BTBLSG2 -- ^ Batch 4
  | BTBLSMLResult -- ^ Batch 4
