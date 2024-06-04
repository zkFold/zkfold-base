{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Symbolic.Data.Maybe (
    Maybe, just, nothing, fromMaybe, isNothing, isJust
) where

import qualified Prelude                            as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Data.Bool
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
    restore _ = Haskell.error "restore ArithmeticCircuit: wrong number of arguments"
    typeSize = 1 + typeSize @a @(u (ArithmeticCircuit a))
