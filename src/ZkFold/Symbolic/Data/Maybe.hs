{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, maybe, just, nothing, fromMaybe, isNothing, isJust, find
) where

import           Data.Function                                          ((.))
import           GHC.Generics                                           (Par1 (..), type (:*:) (..))
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

nothing
    :: forall a u k
    .  SymbolicData a (u (ArithmeticCircuit a Par1))
    => k ~ TypeSize a (u (ArithmeticCircuit a Par1))
    => KnownNat k
    => Maybe u (ArithmeticCircuit a Par1)
nothing = Maybe zero (let ArithmeticCircuit c o = embedV $ Haskell.pure @(Vector k) (zero @a) in restore c o)

fromMaybe
    :: SymbolicData a (u (ArithmeticCircuit a Par1))
    => 1 ~ TypeSize a (u (ArithmeticCircuit a Par1))
    => u (ArithmeticCircuit a Par1)
    -> Maybe u (ArithmeticCircuit a Par1)
    -> u (ArithmeticCircuit a Par1)
fromMaybe a (Maybe h t) =
  let
    as = pieces a
    ts = pieces t
    ArithmeticCircuit c o = (ts - as) * mapOutputs (V.singleton . unPar1) h + as
  in
    restore c o

isNothing :: (DiscreteField b a) => Maybe u a -> b
isNothing (Maybe h _) = isZero h

isJust :: (DiscreteField b a) => Maybe u a -> b
isJust = not Haskell.. isNothing

instance
    ( SymbolicData a (u (ArithmeticCircuit a Par1))
    , k ~ TypeSize a (u (ArithmeticCircuit a Par1))
    , k1 ~ k + 1
    , (k1 - 1) ~ k)
  => SymbolicData a (Maybe u (ArithmeticCircuit a Par1)) where
    type TypeSize a (Maybe u (ArithmeticCircuit a Par1)) = TypeSize a (u (ArithmeticCircuit a Par1)) + 1
    pieces (Maybe h t) = mapOutputs (\(Par1 h' :*: t') -> h' V..: t') $ h `joinCircuits` pieces t
    restore c o = Maybe (c `withOutputs` Par1 (V.head o)) (restore c (V.tail o))

maybe :: forall a b bool f .
    Conditional bool b =>
    DiscreteField bool a =>
    b -> (f a -> b) -> Maybe f a -> b
maybe d h x@(Maybe _ v) = bool @bool d (h v) $ isNothing x

find :: forall a bool f t .
    Haskell.Foldable t =>
    AdditiveMonoid (f a) =>
    Conditional bool (Maybe f a) =>
    DiscreteField bool a =>
    (f a -> bool) -> t (f a) -> Maybe f a
find p = let n = Maybe zero zero in
    foldr (\i r -> maybe @a @_ @bool (bool @bool n (just i) $ p i) (Haskell.const r) r) n
