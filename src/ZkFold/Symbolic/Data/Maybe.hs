{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, isNothing, isJust, find
) where

import           Prelude                                             (foldr, ($))
import qualified Prelude                                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.DiscreteField

data Maybe u a = Maybe a (u a)
  deriving stock
    ( Haskell.Eq
    , Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )

just :: Field a => u a -> Maybe u a
just = Maybe one

nothing :: forall a u. (SymbolicData a (u (ArithmeticCircuit a))) => Maybe u (ArithmeticCircuit a)
nothing = Maybe zero (restore @a (Haskell.replicate (Haskell.fromIntegral (typeSize @a @(u (ArithmeticCircuit a)))) zero))

fromMaybe :: (SymbolicData a (u (ArithmeticCircuit a))) => u (ArithmeticCircuit a) -> Maybe u (ArithmeticCircuit a) -> u (ArithmeticCircuit a)
fromMaybe a (Maybe h t) =
  let
    as = pieces a
    ts = pieces t
    merge a' t' = (t' - a') * h + a'
  in
    restore (Haskell.zipWith merge as ts)

isNothing :: (DiscreteField (Bool a) a) => Maybe u a -> Bool a
isNothing (Maybe h _) = isZero h

isJust :: (DiscreteField (Bool a) a) => Maybe u a -> Bool a
isJust = not Haskell.. isNothing

instance SymbolicData a (u (ArithmeticCircuit a))
  => SymbolicData a (Maybe u (ArithmeticCircuit a)) where
    pieces (Maybe h t) = h : pieces t
    restore (h:ts) = Maybe h (restore ts)
    restore _      = Haskell.error "restore ArithmeticCircuit: wrong number of arguments"
    typeSize = 1 + typeSize @a @(u (ArithmeticCircuit a))

maybe :: forall a b f .
    Conditional (Bool a) b =>
    DiscreteField (Bool a) a =>
    b -> (f a -> b) -> Maybe f a -> b
maybe d h x@(Maybe _ v) = bool @(Bool a) d (h v) $ isNothing x

find :: forall a f t .
    Haskell.Foldable t =>
    AdditiveMonoid (f a) =>
    Conditional (Bool a) (Maybe f a) =>
    DiscreteField (Bool a) a =>
    (f a -> Bool a) -> t (f a) -> Maybe f a
find p = let n = Maybe zero zero in
    foldr (\i r -> maybe (bool @(Bool a) n (just i) $ p i) (Haskell.const r) $ r) n
