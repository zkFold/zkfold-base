{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module ZkFold.UPLC.Evaluation (ExValue (..), MaybeValue (..), eval) where

import           Control.Monad                    (return, (>>=))
import           Data.Either                      (Either (..))
import           Data.Function                    (($), (.))
import           Data.Functor.Rep                 (Representable)
import           Data.List                        (map, null, (++))
import           Data.Maybe                       (Maybe (..))
import           Data.Proxy                       (Proxy (..))
import           Data.Traversable                 (Traversable)
import           Data.Typeable                    (Typeable, cast)
import           Prelude                          (error, fromIntegral)

import           ZkFold.Base.Algebra.Basic.Class  (FromConstant (..))
import           ZkFold.Prelude                   ((!!))
import           ZkFold.Symbolic.Class            (Symbolic)
import           ZkFold.Symbolic.Data.Bool        (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Class       (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional (bool)
import qualified ZkFold.Symbolic.Data.Maybe       as Symbolic
import           ZkFold.UPLC.BuiltinFunction
import           ZkFold.UPLC.BuiltinType
import           ZkFold.UPLC.Term

class
    ( Typeable v, SymbolicData v
    , Context v ~ c, Support v ~ Proxy c
    -- TODO: Remove after Conditional becomes part of SymbolicData
    , Representable (Layout v)
    , Traversable (Layout v)
    ) => IsData (t :: BuiltinType) v c | t c -> v, v -> t, v -> c where
  asPair :: v -> Maybe (ExValue c, ExValue c)

data ExValue c = forall t v. IsData t v c => ExValue v

type Sym c = (Symbolic c, Typeable c)
-- TODO: Add more instances
instance Sym c => IsData BTBool (Bool c) c where asPair _ = Nothing
instance Sym c => IsData BTUnit (Proxy c) c where asPair _ = Nothing
instance
  (Sym c, IsData t v c, IsData t' v' c) => IsData (BTPair t t') (v, v') c where
  asPair (p, q) = Just (ExValue p, ExValue q)

data MaybeValue c = forall t v. IsData t v c => MaybeValue (Symbolic.Maybe c v)

eval :: forall c. Sym c => Term -> [ExValue c] -> MaybeValue c
eval t args = case impl [] t $ map aValue args of
  Just v  -> v
  Nothing -> MaybeValue (Symbolic.nothing :: Symbolic.Maybe c (Proxy c))

type SomeValue c = Maybe (MaybeValue c)
type Thunk c = Either Term (SomeValue c)
type Ctx c = [Thunk c]
data Arg c = ACase [Term] | AThunk (Thunk c)

impl :: Sym c => Ctx c -> Term -> [Arg c] -> SomeValue c
impl ctx (TVariable i) args = case ctx !! i of
  Left t  -> impl ctx t args
  Right v -> if null args then v else Nothing
impl _ (TConstant c) [] = someValue (evalConstant c)
impl _ (TConstant _) (_:_) = Nothing
impl ctx (TBuiltin (BFMono f)) args =
  applyMono true (evalMono f) [evalArg ctx a [] | a <- args]
impl ctx (TBuiltin (BFPoly f)) args = applyPoly ctx f args
impl _ (TLam _) [] = Nothing
impl _ (TLam _) (ACase _:_) = Nothing
impl ctx (TLam f) (AThunk t:args) = impl (t:ctx) f args
impl ctx (TApp f x) args = impl ctx f (aTerm x : args)
impl ctx (TDelay t) args = impl ctx t args
impl ctx (TForce t) args = impl ctx t args
impl ctx (TConstr t f) (ACase bs:args) =
  impl ctx (bs !! fromIntegral t) (map aTerm f ++ args)
impl _ (TConstr _ _) [] = error "FIXME: UPLC Data support"
impl _ (TConstr _ _) (_:_) = Nothing
impl ctx (TCase s bs) args = impl ctx s (ACase bs : args)
impl _ TError _ = Nothing

evalArg :: Sym c => Ctx c -> Arg c -> [Arg c] -> SomeValue c
evalArg _ (ACase _) _              = Nothing
evalArg ctx (AThunk (Left t)) args = impl ctx t args
evalArg _ (AThunk (Right v)) []    = v
evalArg _ (AThunk (Right _)) (_:_) = Nothing

someValue :: Sym c => SymValue t c -> SomeValue c
someValue (SymValue v) = Just $ MaybeValue (Symbolic.just v)

aTerm :: Term -> Arg c
aTerm = AThunk . Left

aValue :: Sym c => ExValue c -> Arg c
aValue (ExValue v) = AThunk . Right . Just $ MaybeValue (Symbolic.just v)

applyMono :: Sym c => Bool c -> Fun s t c -> [SomeValue c] -> SomeValue c
applyMono b (FSat x) []       = Just $ MaybeValue (bool Symbolic.nothing x b)
applyMono _ (FSat _) (_:_)    = Nothing
applyMono _ (FLam _) []       = Nothing
applyMono b (FLam f) (v:args) = cast v >>= \x -> applyMono b (f x) args

applyPoly :: Sym c => Ctx c -> BuiltinPolyFunction s t -> [Arg c] -> SomeValue c
applyPoly ctx IfThenElse (ct:tt:et:args) = do
  MaybeValue c0 <- evalArg ctx ct []
  MaybeValue t <- evalArg ctx tt args
  MaybeValue e0 <- evalArg ctx et args
  c :: Bool c <- cast c0
  e <- cast e0
  return $ MaybeValue (bool e t c)
applyPoly ctx ChooseUnit (_:t:args) = evalArg ctx t args
applyPoly ctx Trace (_:t:args) = evalArg ctx t args
applyPoly ctx FstPair [arg] = do
  MaybeValue p <- evalArg ctx arg []
  (ExValue v, _) <- asPair (Symbolic.fromJust p)
  return $ MaybeValue (symMaybe p v)
applyPoly ctx SndPair [arg] = do
  MaybeValue p <- evalArg ctx arg []
  (_, ExValue v) <- asPair (Symbolic.fromJust p)
  return $ MaybeValue (symMaybe p v)
applyPoly _ (BPFList _) _ = error "FIXME: UPLC List support"
applyPoly _ ChooseData _ = error "FIXME: UPLC Data support"
applyPoly _ _ _ = Nothing

symMaybe :: (Sym c, IsData d t c) => Symbolic.Maybe c u -> t -> Symbolic.Maybe c t
symMaybe b v = bool Symbolic.nothing (Symbolic.just v) (Symbolic.isJust b)

data SymValue t c = forall v. IsData t v c => SymValue v

evalConstant :: Sym c => Constant t -> SymValue t c
evalConstant (CBool b)       = SymValue (if b then true else false)
evalConstant (CInteger _)    = error "FIXME: UPLC Integer support"
evalConstant (CByteString _) = error "FIXME: UPLC ByteString support"
evalConstant (CString _)     = error "FIXME: UPLC String support"
evalConstant (CUnit ())      = SymValue Proxy
evalConstant (CData _)       = error "FIXME: UPLC Data support"
evalConstant (CList _)       = error "FIXME: UPLC List support"
evalConstant (CPair p q)     = pair (evalConstant p) (evalConstant q)
evalConstant (CG1 _)         = error "FIXME: UPLC BLS support"
evalConstant (CG2 _)         = error "FIXME: UPLC BLS support"

pair :: Sym c => SymValue t c -> SymValue u c -> SymValue (BTPair t u) c
pair (SymValue p) (SymValue q) = SymValue (p, q)

data Fun (s :: [BuiltinType]) (t :: BuiltinType) c where
  FSat :: IsData t v c => Symbolic.Maybe c v -> Fun '[] t c
  FLam :: IsData s v c => (v -> Fun ss t c) -> Fun (s ': ss) t c

instance IsData t v c => FromConstant (Symbolic.Maybe c v) (Fun '[] t c) where
  fromConstant = FSat

instance
    (IsData s v c, FromConstant f (Fun ss t c))
    => FromConstant (v -> f) (Fun (s ': ss) t c) where
  fromConstant f = FLam (fromConstant . f)

evalMono :: Sym c => BuiltinMonoFunction s t -> Fun s t c
evalMono (BMFInteger _)    = error "FIXME: UPLC Integer support"
evalMono (BMFByteString _) = error "FIXME: UPLC ByteString support"
evalMono (BMFString _)     = error "FIXME: UPLC String support"
evalMono (BMFAlgorithm _)  = error "FIXME: UPLC Algorithms support"
evalMono (BMFData _)       = error "FIXME: UPLC Data support"
evalMono (BMFCurve _)      = error "FIXME: UPLC Curve support"
evalMono (BMFBitwise _)    = error "FIXME: UPLC ByteString support"
