{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, fromJust, isNothing, isJust, find
) where

import           Data.Functor                     ((<$>))
import           Data.Functor.Rep                 (pureRep)
import           GHC.Generics                     (Generic, Par1 (..))
import           Prelude                          (foldr, type (~), ($))
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq

data Maybe context x = Maybe { isJust :: Bool context, fromJust :: x }
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    , Generic
    )

deriving stock instance (Haskell.Eq (context Par1), Haskell.Eq x) => Haskell.Eq (Maybe context x)

instance (SymbolicOutput x, Context x ~ c) => SymbolicData (Maybe c x) where
instance (SymbolicOutput x, Context x ~ c, Conditional (Bool c) x) => Conditional (Bool c) (Maybe c x)
instance (Context x ~ c, SymbolicEq x) => Eq (Maybe c x)

just :: Symbolic c => x -> Maybe c x
just = Maybe true

nothing ::
  forall x c .
  (SymbolicData x, Context x ~ c) =>
  Maybe c x
nothing =
  Maybe false $ restore $ Haskell.const (embed (pureRep zero), pureRep zero)

fromMaybe ::
  forall c x .
  Conditional (Bool c) x =>
  x -> Maybe c x -> x
fromMaybe a (Maybe j t) = bool a t j

isNothing :: Symbolic c => Maybe c x -> Bool c
isNothing (Maybe h _) = not h

maybe :: forall a b c .
    Conditional (Bool c) b =>
    b -> (a -> b) -> Maybe c a -> b
maybe d h m = fromMaybe d (h <$> m)

find :: forall a c t .
    (SymbolicOutput a, Context a ~ c, Haskell.Foldable t, Conditional (Bool c) a) =>
    (a -> Bool c) -> t a -> Maybe c a
find p = let n = nothing in
    foldr (\i r -> maybe @a @_ @c (bool @(Bool c) n (just i) $ p i) (Haskell.const r) r) n
