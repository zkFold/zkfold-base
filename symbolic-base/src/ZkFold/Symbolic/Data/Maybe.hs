{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, fromJust, isNothing, isJust, find
) where

import           Data.Functor                     ((<$>))
import           Data.Functor.Rep                 (Representable, pureRep)
import           Data.Proxy                       (Proxy)
import           Data.Traversable                 (Traversable)
import           GHC.Generics                     (Generic, Par1 (..))
import           Prelude                          (foldr, type (~), ($))
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative (HApplicative)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional

data Maybe context x = Maybe { isJust :: Bool context, fromJust :: x }
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    , Generic
    )

deriving stock instance (Haskell.Eq (context Par1), Haskell.Eq x) => Haskell.Eq (Maybe context x)

just :: Symbolic c => x -> Maybe c x
just = Maybe true

nothing ::
  forall x c .
  ( SymbolicData x, Representable (Layout x)
  , Representable (Payload x), Context x ~ c, Symbolic c) =>
  Maybe c x
nothing =
  Maybe false $ restore $ Haskell.const (embed (pureRep zero), pureRep zero)

fromMaybe ::
  forall c x .
  ( Symbolic c, SymbolicData x, Context x ~ c, Traversable (Layout x)
  , Representable (Layout x), Representable (Payload x)) =>
  x -> Maybe c x -> x
fromMaybe a (Maybe j t) = bool a t j

isNothing :: Symbolic c => Maybe c x -> Bool c
isNothing (Maybe h _) = not h

instance
    ( HApplicative c
    , SymbolicData x
    , Context x ~ c
    , Support x ~ Proxy c
    ) => SymbolicData (Maybe c x) where

maybe :: forall a b c .
    ( Symbolic c, SymbolicData b, Context b ~ c, Representable (Layout b)
    , Traversable (Layout b), Representable (Payload b)) =>
    b -> (a -> b) -> Maybe c a -> b
maybe d h m = fromMaybe d (h <$> m)

find :: forall a c t .
    ( Symbolic c, SymbolicData a, Context a ~ c, Support a ~ Proxy c
    , Representable (Layout a), Traversable (Layout a)
    , Representable (Payload a), Haskell.Foldable t) =>
    (a -> Bool c) -> t a -> Maybe c a
find p = let n = nothing in
    foldr (\i r -> maybe @a @_ @c (bool @(Bool c) n (just i) $ p i) (Haskell.const r) r) n
