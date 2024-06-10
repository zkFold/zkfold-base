{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, isNothing, isJust, mapMaybe, find
) where

import           GHC.Generics
import qualified Prelude                                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Data.Bool

data Maybe u a = Maybe a (u a)
  deriving stock
    ( Haskell.Eq
    , Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    , Generic1
    )

deriving via Generically1 (Maybe u) instance
  VectorSpace a u => VectorSpace a (Maybe u)

just :: MultiplicativeMonoid a => u a -> Maybe u a
just = Maybe one

nothing :: (AdditiveMonoid a, VectorSpace a u) => Maybe u a
nothing = Maybe zero zeroV

fromMaybe :: (Ring a, VectorSpace a u) => u a -> Maybe u a -> u a
fromMaybe d (Maybe j x) = scaleV j (x `subtractV` d) `addV` d

isJust :: Maybe u a -> Bool a
isJust (Maybe j _) = Bool j

isNothing :: Ring a => Maybe u a -> Bool a
isNothing (Maybe j _) = Bool (one - j)

instance SymbolicData a (u (ArithmeticCircuit a))
  => SymbolicData a (Maybe u (ArithmeticCircuit a)) where
    pieces (Maybe h t) = h : pieces t
    restore (h:ts) = Maybe h (restore ts)
    restore _      = Haskell.error "restore ArithmeticCircuit: wrong number of arguments"
    typeSize = 1 + typeSize @a @(u (ArithmeticCircuit a))

mapMaybe :: (u a -> v a) -> Maybe u a -> Maybe v a
mapMaybe h (Maybe j u) = Maybe j (h u)

maybe
  :: (Ring a, VectorSpace a v)
  => v a -> (u a -> v a) -> Maybe u a -> v a
maybe d h m = fromMaybe d (mapMaybe h m)

find
  :: (Ring a, VectorSpace a u, Haskell.Foldable f)
  => (u a -> Bool a) -> (f :.: u) a -> Maybe u a
find p
  = Haskell.foldr
      (\i r -> maybe (bool nothing (just i) (p i)) (Haskell.const r) r)
      nothing
  Haskell.. unComp1
