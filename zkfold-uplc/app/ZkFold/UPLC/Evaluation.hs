{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.UPLC.Evaluation where

import           Data.Kind                   (Type)
import           Data.Proxy                  (Proxy (..))
import           Data.Tuple                  (fst, snd)
import           Prelude                     (error)

import           ZkFold.Symbolic.Class       (Symbolic)
import           ZkFold.Symbolic.Data.Bool   (Bool, BoolType (..))
import           ZkFold.UPLC.BuiltinFunction
import           ZkFold.UPLC.BuiltinType
import           ZkFold.UPLC.Term

type Context = (Type -> Type) -> Type

type family Eval (t :: BuiltinType) (c :: Context) :: Type where
  -- TODO: add support for more types
  Eval BTBool c = Bool c
  Eval BTUnit c = Proxy c
  Eval (BTPair t u) c = (Eval t c, Eval u c)

type family EvalFun (s :: [BuiltinType]) (t :: BuiltinType) (c :: Context) where
  EvalFun '[] t c = Eval t c
  EvalFun (s ': ss) t c = Eval s c -> EvalFun ss t c

evalConstant :: forall c t. Symbolic c => Constant t -> Eval t c
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

evalBuiltin :: forall c s t. Symbolic c => BuiltinFunction s t -> EvalFun s t c
evalBuiltin (BFMono f) = evalMono @c f
evalBuiltin (BFPoly f) = evalPoly @c f

evalPoly :: forall c s t. Symbolic c => BuiltinPolyFunction s t -> EvalFun s t c
evalPoly IfThenElse  = error "FIXME: UPLC IfThenElse"
evalPoly ChooseUnit  = \_ x -> x
evalPoly Trace       = \_ x -> x
evalPoly FstPair     = fst
evalPoly SndPair     = snd
evalPoly (BPFList _) = error "FIXME: UPLC List support"
evalPoly ChooseData  = error "FIXME: UPLC Data support"

evalMono :: forall c s t. Symbolic c => BuiltinMonoFunction s t -> EvalFun s t c
evalMono (BMFInteger _)    = error "FIXME: UPLC Integer support"
evalMono (BMFByteString _) = error "FIXME: UPLC ByteString support"
evalMono (BMFString _)     = error "FIXME: UPLC String support"
evalMono (BMFAlgorithm _)  = error "FIXME: UPLC Algorithms support"
evalMono (BMFData _)       = error "FIXME: UPLC Data support"
evalMono (BMFCurve _)      = error "FIXME: UPLC Curve support"
evalMono (BMFBitwise _)    = error "FIXME: UPLC ByteString support"
