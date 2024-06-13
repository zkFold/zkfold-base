{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, isNothing, isJust, find
) where

import           Prelude                                                (foldr, type (~), ($))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                                as V
import           ZkFold.Base.Data.Vector                                (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (embedV)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance    ()
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

nothing :: forall a u k. (SymbolicData a k (u (ArithmeticCircuit 1 a))) => Maybe u (ArithmeticCircuit 1 a)
nothing = Maybe zero (let ArithmeticCircuit c o = embedV $ Haskell.pure @(Vector k) (zero @a) in restore c o)

fromMaybe :: (SymbolicData a 1 (u (ArithmeticCircuit 1 a))) => u (ArithmeticCircuit 1 a) -> Maybe u (ArithmeticCircuit 1 a) -> u (ArithmeticCircuit 1 a)
fromMaybe a (Maybe h t) =
  let
    as = pieces a
    ts = pieces t
    merge a' t' = (t' - a') * h + a'
    ArithmeticCircuit c o = merge as ts
  in
    restore c o

isNothing :: (DiscreteField (Bool a) a) => Maybe u a -> Bool a
isNothing (Maybe h _) = isZero h

isJust :: (DiscreteField (Bool a) a) => Maybe u a -> Bool a
isJust = not Haskell.. isNothing

instance (SymbolicData a k (u (ArithmeticCircuit 1 a)), KnownNat k1, k1 ~ 1 + k, (k1 - 1) ~ k)
  => SymbolicData a k1 (Maybe u (ArithmeticCircuit 1 a)) where
    pieces (Maybe h t) = h `joinCircuits` pieces t
    restore c o = Maybe (c `withOutputs` V.take @1 o) (restore c (V.drop @1 o))

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
