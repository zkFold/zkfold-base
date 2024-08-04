{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, isNothing, isJust, find
) where

import           Data.Function                                       ((.))
import           GHC.Generics                                        (Par1 (..))
import           Prelude                                             (foldr, type (~), ($))
import qualified Prelude                                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Control.HApplicative                    (HApplicative, hliftA2)
import           ZkFold.Base.Data.HFunctor                           (HFunctor, hmap)
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional

data Maybe context x = Maybe (Bool context) x
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )

deriving stock instance (Haskell.Eq (context Par1), Haskell.Eq x) => Haskell.Eq (Maybe context x)

just :: Symbolic c => x -> Maybe c x
just = Maybe true

nothing
    :: forall c x k
    .  Symbolic c
    => SymbolicData c x
    => k ~ TypeSize c x
    => KnownNat k
    => Maybe c x
nothing = Maybe false (let c = embed @c $ Haskell.pure @(Vector k) zero in restore (Haskell.const c))

fromMaybe
    :: forall c x
    .  HFunctor c
    => Ring (c (Vector 1))
    => SymbolicData c x
    => 1 ~ TypeSize c x
    => x
    -> Maybe c x
    -> x
fromMaybe a (Maybe (Bool h) t) = restore $ \i ->
  let
    as = pieces a i
    ts = pieces t i
  in
    (ts - as) * hmap (V.singleton . unPar1) h + as

isNothing :: Symbolic c => Maybe c x -> Bool c
isNothing (Maybe h _) = not h

isJust :: Maybe c x -> Bool c
isJust (Maybe h _) = h

instance
    ( HApplicative c
    , SymbolicData c x
    , Support c x ~ ()
    , k ~ TypeSize c x
    , k1 ~ k + 1
    , (k1 - 1) ~ k)
  => SymbolicData c (Maybe c x) where
    type Support c (Maybe c x) = ()
    type TypeSize c (Maybe c x) = TypeSize c x + 1
    pieces (Maybe (Bool h) t) i = hliftA2 (\(Par1 h') t' -> h' V..: t') h (pieces t i)
    restore f = Maybe (restore (hmap V.take . f)) (restore (hmap V.tail . f))

maybe :: forall a b c .
    Symbolic c =>
    Conditional (Bool c) b =>
    b -> (a -> b) -> Maybe c a -> b
maybe d h x@(Maybe _ v) = bool @(Bool c) d (h v) $ isNothing x

find :: forall a c t .
    Symbolic c =>
    SymbolicData c a =>
    KnownNat (TypeSize c a) =>
    Haskell.Foldable t =>
    Conditional (Bool c) (Maybe c a) =>
    (a -> Bool c) -> t a -> Maybe c a
find p = let n = nothing in
    foldr (\i r -> maybe @a @_ @c (bool @(Bool c) n (just i) $ p i) (Haskell.const r) r) n
