{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.UPLC.Evaluation where

import           Data.Function               (const, (.))
import           Data.Kind                   (Type)
import           Data.Proxy                  (Proxy (..))
import           Data.Tuple                  (fst, snd)
import           Prelude                     (error)

import           ZkFold.Symbolic.Class       (Symbolic)
import           ZkFold.Symbolic.Data.Bool   (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Maybe  (Maybe, just)
import           ZkFold.UPLC.BuiltinFunction
import           ZkFold.UPLC.BuiltinType
import           ZkFold.UPLC.Term

type Context = (Type -> Type) -> Type

type family ValueOf (t :: BuiltinType) (c :: Context) where
  -- TODO: Add support for more types
  ValueOf BTBool c = Bool c
  ValueOf BTUnit c = Proxy c
  ValueOf (BTPair t u) c = (ValueOf t c, ValueOf u c)

type family FunOf (s :: [BuiltinType]) (t :: BuiltinType) (c :: Context) where
  FunOf '[] t c = Maybe c (ValueOf t c)
  FunOf (s ': ss) t c = ValueOf s c -> FunOf ss t c

evalConstant :: forall c t. Symbolic c => Constant t -> ValueOf t c
evalConstant (CBool b)       = if b then true else false
evalConstant (CInteger _)    = error "FIXME: UPLC Integer support"
evalConstant (CByteString _) = error "FIXME: UPLC ByteString support"
evalConstant (CString _)     = error "FIXME: UPLC String support"
evalConstant (CUnit ())      = Proxy
evalConstant (CData _)       = error "FIXME: UPLC Data support"
evalConstant (CList _)       = error "FIXME: UPLC List support"
evalConstant (CPair p q)     = (evalConstant @c p, evalConstant @c q)
evalConstant (CG1 _)         = error "FIXME: UPLC BLS support"
evalConstant (CG2 _)         = error "FIXME: UPLC BLS support"

evalBuiltin :: forall c s t. Symbolic c => BuiltinFunction s t -> FunOf s t c
evalBuiltin (BFMono f) = evalMono @c f
evalBuiltin (BFPoly f) = evalPoly @c f

evalPoly :: forall c s t. Symbolic c => BuiltinPolyFunction s t -> FunOf s t c
evalPoly IfThenElse  = error "FIXME: UPLC IfThenElse"
evalPoly ChooseUnit  = const just
evalPoly Trace       = const just
evalPoly FstPair     = just . fst
evalPoly SndPair     = just . snd
evalPoly (BPFList _) = error "FIXME: UPLC List support"
evalPoly ChooseData  = error "FIXME: UPLC Data support"

evalMono :: forall c s t. Symbolic c => BuiltinMonoFunction s t -> FunOf s t c
evalMono (BMFInteger _)    = error "FIXME: UPLC Integer support"
evalMono (BMFByteString _) = error "FIXME: UPLC ByteString support"
evalMono (BMFString _)     = error "FIXME: UPLC String support"
evalMono (BMFAlgorithm _)  = error "FIXME: UPLC Algorithms support"
evalMono (BMFData _)       = error "FIXME: UPLC Data support"
evalMono (BMFCurve _)      = error "FIXME: UPLC Curve support"
evalMono (BMFBitwise _)    = error "FIXME: UPLC ByteString support"
