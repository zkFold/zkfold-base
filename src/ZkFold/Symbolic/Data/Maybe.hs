{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe,
    maybe,
    just,
    nothing,
    fromMaybe,
    isNothing,
    isJust,
    find,
) where

import           GHC.Generics
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Functor

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

maybe
  :: (Ring a, VectorSpace a v)
  => v a -> (u a -> v a) -> Maybe u a -> v a
maybe d h m = fromMaybe d (fmap h m)

fromMaybe :: (Ring a, VectorSpace a u) => u a -> Maybe u a -> u a
fromMaybe d (Maybe j u) = bool d u j

isNothing :: Ring a => Maybe u a -> Bool a
isNothing = not Haskell.. isJust

instance Functor Maybe where
  fmap h (Maybe j u) = Maybe j (h u)

instance Applicative Maybe where
  return = just
  zipWith f (Maybe ju u) (Maybe jv v) = Maybe (ju && jv) (f u v)

instance Monad Maybe where
  Maybe j u >>= f = bool nothing (f u) j

instance (Ring a, VectorSpace a u) => Haskell.Monoid (Maybe u a) where
  mempty = nothing

instance (Ring a, VectorSpace a u) => Haskell.Semigroup (Maybe u a) where
  m0 <> m1 = ifThenElse (isJust m0) m0 m1

find
  :: (Ring a, VectorSpace a u, Haskell.Foldable f)
  => (u a -> Bool a) -> (f :.: u) a -> Maybe u a
find p (Comp1 us) = Haskell.foldMap (\i -> bool nothing (just i) (p i)) us
