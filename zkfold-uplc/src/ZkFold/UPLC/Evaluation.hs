{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module ZkFold.UPLC.Evaluation where

import           Data.Bool                        (otherwise)
import           Data.Functor.Rep                 (Representable)
import           Data.List                        ((++))
import qualified Data.Maybe                       as Haskell
import           Data.Ord                         ((>=))
import           Data.Proxy                       (Proxy (..))
import           Data.Typeable                    (Typeable, cast)
import           Prelude                          (Traversable, error)

import           ZkFold.Prelude                   (length, splitAt, (!!))
import           ZkFold.Symbolic.Class            (Symbolic)
import           ZkFold.Symbolic.Data.Bool        (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Class       (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional (bool)
import           ZkFold.Symbolic.Data.Maybe       (Maybe, fromJust, isJust, just, maybe, nothing)
import           ZkFold.UPLC.BuiltinFunction
import           ZkFold.UPLC.BuiltinType
import           ZkFold.UPLC.Normalization
import           ZkFold.UPLC.Term

type family Value (t :: BuiltinType) c where
  -- TODO: Add support for more types
  Value BTBool c = Bool c
  Value BTUnit c = Proxy c
  Value (BTPair t u) c = (Value t c, Value u c)

type IsData t v c =
  ( Value t c ~ v, Typeable v, SymbolicData v
  , Context v ~ c, Support v ~ Proxy c
  -- TODO: Remove after Conditional becomes part of SymbolicData
  , Representable (Layout v)
  , Traversable (Layout v))

data SymValue t c = forall v. IsData t v c => SymValue v

data Fun (s :: [BuiltinType]) (t :: BuiltinType) c where
  FSat :: IsData t v c => Maybe c v -> Fun '[] t c
  FLam :: IsData s v c => (v -> Fun ss t c) -> Fun (s ': ss) t c

data SomeValue c = SomeError | forall t v . IsData t v c => SomeValue (Maybe c v)

type Sym c = (Symbolic c, Typeable c)

evalNormalized :: forall c. Sym c => Normalized -> [SomeValue c] -> SomeValue c
evalNormalized = implN []
  where
    implN :: [SomeValue c] -> Normalized -> [SomeValue c] -> SomeValue c
    implN ctx (NLam n body) args
      | length args >= n = let (ctx', args') = splitAt n args
                            in implB (ctx' ++ ctx) body args'
      | otherwise = error "Not enough arguments"

    implB :: [SomeValue c] -> BodyNF -> [SomeValue c] -> SomeValue c
    implB ctx (NCall call) args = implC ctx call args
    implB _ (NConstant @t c) [] =
      case evalConstant @c c of
        SymValue v -> SomeValue @c @t (just v)
    implB _ (NConstant _) _     = error "Applying args to constant"
    implB _ (NConstr _ _) _     = error "FIXME: UPLC Constructor support"
    implB _ NError _            = SomeError

    implC :: [SomeValue c] -> CallNF -> [SomeValue c] -> SomeValue c
    implC ctx (NApp head args') args  = implH ctx head ([implN ctx a [] | a <- args'] ++ args)
    implC _ (NCase _ _) _             = error "FIXME: UPLC Constructor support"
    implC ctx (NPoly head args') args = implP ctx head args' args

    implH :: [SomeValue c] -> HeadNF -> [SomeValue c] -> SomeValue c
    implH ctx (NVariable i) []   = ctx !! i
    implH _ (NVariable _) _      = error "Applying args to value"
    implH _ (NMono @s @t f) args = apply true (evalMono @c @s @t f) args

    apply :: Bool c -> Fun s t c -> [SomeValue c] -> SomeValue c
    apply b (FSat @t x) [] =
      SomeValue @_ @t (maybe nothing (\x' -> bool nothing (just x') b) x)
    apply _ (FSat _) _ = error "Applying args to value"
    apply _ (FLam _) [] = error "Not enough arguments"
    apply b (FLam @u f) (a:as) = case a of
      SomeError -> let x = fromJust nothing in apply false (f x) as
      SomeValue x0 -> apply (b && isJust x0) (f x) as
        where x = Haskell.fromMaybe (error "Wrong argument type") (cast x0)

    implP :: [SomeValue c] -> BuiltinPolyFunction s t -> Untyped s Normalized -> [SomeValue c] -> SomeValue c
    implP ctx IfThenElse (c ::: t ::: e ::: UNil) args =
      case (implN ctx c [], implN ctx t args, implN ctx e args) of
        (SomeValue c0, SomeValue @_ @t tb, SomeValue e0) -> case (cast c0, cast e0) of
          (Haskell.Just (cond :: Bool c), Haskell.Just eb) -> SomeValue @c @t (bool eb tb cond)
          _                                                -> error "Wrong argument types"
        _ -> SomeError
    implP ctx ChooseUnit (_ ::: t ::: UNil) args = implN ctx t args
    implP ctx Trace (_ ::: t ::: UNil) args = implN ctx t args
    implP _ FstPair (_ ::: UNil) _ = _
    implP _ SndPair (_ ::: UNil) _ = _
    implP _ (BPFList _) _ _ = error "FIXME: UPLC List support"
    implP _ ChooseData _ _ = error "FIXME: UPLC Data support"

evalConstant :: forall c t. Sym c => Constant t -> SymValue t c
evalConstant (CBool b)       = SymValue (if b then true else false)
evalConstant (CInteger _)    = error "FIXME: UPLC Integer support"
evalConstant (CByteString _) = error "FIXME: UPLC ByteString support"
evalConstant (CString _)     = error "FIXME: UPLC String support"
evalConstant (CUnit ())      = SymValue Proxy
evalConstant (CData _)       = error "FIXME: UPLC Data support"
evalConstant (CList _)       = error "FIXME: UPLC List support"
evalConstant (CPair p q)     =
  case (evalConstant @c p, evalConstant @c q) of
    (SymValue u, SymValue v) -> SymValue (u, v)
evalConstant (CG1 _)         = error "FIXME: UPLC BLS support"
evalConstant (CG2 _)         = error "FIXME: UPLC BLS support"

evalMono :: forall c s t. Sym c => BuiltinMonoFunction s t -> Fun s t c
evalMono (BMFInteger _)    = error "FIXME: UPLC Integer support"
evalMono (BMFByteString _) = error "FIXME: UPLC ByteString support"
evalMono (BMFString _)     = error "FIXME: UPLC String support"
evalMono (BMFAlgorithm _)  = error "FIXME: UPLC Algorithms support"
evalMono (BMFData _)       = error "FIXME: UPLC Data support"
evalMono (BMFCurve _)      = error "FIXME: UPLC Curve support"
evalMono (BMFBitwise _)    = error "FIXME: UPLC ByteString support"
