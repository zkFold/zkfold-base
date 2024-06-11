{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, isNothing, isJust, mapMaybe, find
) where

import           GHC.Generics
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Bool

data Maybe u a = Maybe {isJust :: Bool a, maybeVal :: u a}
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    , Generic1
    )

deriving via Generically1 (Maybe u) instance
  VectorSpace a u => VectorSpace a (Maybe u)

just :: Ring a => u a -> Maybe u a
just = Maybe true

nothing :: (Ring a, VectorSpace a u) => Maybe u a
nothing = Maybe false zeroV

fromMaybe :: (Ring a, VectorSpace a u) => u a -> Maybe u a -> u a
fromMaybe d (Maybe j x) = bool d x j

isNothing :: Ring a => Maybe u a -> Bool a
isNothing = not Haskell.. isJust

mapMaybe :: (u a -> v a) -> Maybe u a -> Maybe v a
mapMaybe h (Maybe j u) = Maybe j (h u)

maybe
  :: (Ring a, VectorSpace a v)
  => v a -> (u a -> v a) -> Maybe u a -> v a
maybe d h m = fromMaybe d (mapMaybe h m)

find
  :: (Ring a, VectorSpace a u, Haskell.Foldable f)
  => (u a -> Bool a) -> (f :.: u) a -> Maybe u a
find p =
  let
    finder i r@(Maybe j _) =
      fromMaybe (bool nothing (just i) (p i)) (Maybe j r)
  in
    Haskell.foldr finder nothing Haskell.. unComp1
