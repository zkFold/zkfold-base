{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, fromJust, isNothing, isJust, find
) where

import           Data.Function                    ((.))
import           Data.Functor.Rep                 (Representable, pureRep)
import           Data.Proxy                       (Proxy)
import           Data.Traversable                 (Traversable)
import           GHC.Generics                     (Par1 (..))
import           Prelude                          (foldr, type (~), ($))
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative (HApplicative)
import           ZkFold.Base.Data.HFunctor        (HFunctor, hmap)
import qualified ZkFold.Base.Data.Vector          as V
import           ZkFold.Base.Data.Vector          (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional

data Maybe context x = Maybe { isJust :: Bool context, fromJust :: x }
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )

deriving stock instance (Haskell.Eq (context Par1), Haskell.Eq x) => Haskell.Eq (Maybe context x)

just :: Symbolic c => x -> Maybe c x
just = Maybe true

nothing ::
  forall x c .
  (SymbolicData x, Representable (Layout x), Context x ~ c, Symbolic c) =>
  Maybe c x
nothing = Maybe false (let c = embed @c $ pureRep zero in restore (Haskell.const c))

fromMaybe
    :: forall c x
    .  HFunctor c
    => Ring (c (Vector 1))
    => SymbolicData x
    => Context x ~ c
    => Layout x ~ Vector 1
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

instance
    ( HApplicative c
    , SymbolicData x
    , Context x ~ c
    , Support x ~ Proxy c
    ) => SymbolicData (Maybe c x) where

    type Context (Maybe c x) = Context (Bool c, x)
    type Support (Maybe c x) = Support (Bool c, x)
    type Layout (Maybe c x) = Layout (Bool c, x)

    pieces (Maybe b t) = pieces (b, t)
    restore f = let (b, t) = restore f in Maybe b t

maybe :: forall a b c .
    (Symbolic c, SymbolicData b, Context b ~ c) =>
    (Representable (Layout b), Traversable (Layout b)) =>
    b -> (a -> b) -> Maybe c a -> b
maybe d h x@(Maybe _ v) = bool @(Bool c) d (h v) $ isJust x

find :: forall a c t .
    (Symbolic c, SymbolicData a, Context a ~ c, Support a ~ Proxy c) =>
    (Representable (Layout a), Traversable (Layout a)) =>
    Haskell.Foldable t =>
    (a -> Bool c) -> t a -> Maybe c a
find p = let n = nothing in
    foldr (\i r -> maybe @a @_ @c (bool @(Bool c) n (just i) $ p i) (Haskell.const r) r) n
