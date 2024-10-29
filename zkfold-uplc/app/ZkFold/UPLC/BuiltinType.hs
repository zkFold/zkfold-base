{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}

module ZkFold.UPLC.BuiltinType where

import           Data.Data                        (Proxy)
import           Data.Kind                        (Type)
import           GHC.TypeError                    (ErrorMessage (Text), TypeError)

import           ZkFold.Symbolic.Data.Bool        (Bool)

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

type Context = (Type -> Type) -> Type

type family Eval (t :: BuiltinType) (c :: Context) :: Type where
  Eval BTInteger _ = TypeError (Text "FIXME: BigInteger support in UPLC")
  Eval BTByteString _ = TypeError (Text "FIXME: unsized ByteString support in UPLC")
  Eval BTString _ = TypeError (Text "FIXME: String support in UPLC")
  Eval BTBool c = Bool c
  Eval BTUnit c = Proxy c
  Eval BTData _ = TypeError (Text "FIXME: Data support in UPLC")
  Eval (BTList _) _ = TypeError (Text "FIXME: List support in UPLC")
  Eval (BTPair t u) c = (Eval t c, Eval u c)
  Eval BTBLSG1 _ = TypeError (Text "FIXME: BLS support in UPLC")
  Eval BTBLSG2 _ = TypeError (Text "FIXME: BLS support in UPLC")
  Eval BTBLSMLResult _ = TypeError (Text "FIXME: BLS support in UPLC")
