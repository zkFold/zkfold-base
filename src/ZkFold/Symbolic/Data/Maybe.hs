{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, just, nothing, fromMaybe, isNothing, isJust
) where

import           Data.Distributive
import           Data.Functor.Adjunction
import           Data.Functor.Rep
import           Prelude ((.), (<$>))
import qualified Prelude                            as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.DiscreteField

data Maybe u a = Maybe {headMaybe :: a, tailMaybe :: u a}
  deriving stock
    ( Haskell.Eq
    , Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )

just :: Field a => u a -> Maybe u a
just = Maybe one

nothing :: (Field a, Representable u) => Maybe u a
nothing = Maybe zero (tabulate (Haskell.const zero))

fromMaybe :: (Field a, Representable u) => u a -> Maybe u a -> u a
fromMaybe a (Maybe h t) =
  mzipWithRep (\a' t' -> (t' - a') * h + a') a t

isNothing :: (DiscreteField (Bool a) a) => Maybe u a -> Bool a
isNothing = isZero . headMaybe

isJust :: (DiscreteField (Bool a) a) => Maybe u a -> Bool a
isJust = not . isNothing

instance Distributive u => Distributive (Maybe u) where
  distribute fmu = Maybe
    (headMaybe <$> fmu)
    (distribute (tailMaybe <$> fmu))

instance Representable u => Representable (Maybe u) where
  type Rep (Maybe u) = Haskell.Maybe (Rep u)
  tabulate g = Maybe
    (g Haskell.Nothing)
    (tabulate (g . Haskell.Just))
  index (Maybe h _) Haskell.Nothing  = h
  index (Maybe _ t) (Haskell.Just x) = index t x

data Maybe1 f a
  = Nothing1 a
  | Just1 (f a)
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )

instance (Adjunction f u) => Adjunction (Maybe1 f) (Maybe u) where
  unit a = Maybe (Nothing1 a) (leftAdjunct Just1 a)
  counit (Nothing1 h) = headMaybe h
  counit (Just1 t)    = rightAdjunct tailMaybe t
