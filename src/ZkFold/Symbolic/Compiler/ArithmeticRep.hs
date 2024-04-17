{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticRep (
    ArithmeticRepresentable (..)
    , mapArithmetic
    , pureArithmetic
    , bindArithmetic
    , zipWithArithmetic
    , zipWith3Arithmetic
    ) where

import Data.Functor.Rep
import Data.Kind (Type)
import Data.Void
import GHC.Generics ((:.:)(..), (:*:)(..), U1(..))
import Prelude

import ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic)

class Arithmetic a => ArithmeticRepresentable a u where
  type ArithmeticRep a u :: Type
  tabulateArithmetic :: (ArithmeticRep a u -> a) -> u a
  indexArithmetic :: u a -> ArithmeticRep a u -> a

instance Arithmetic a => ArithmeticRepresentable a U1 where
  type ArithmeticRep a U1 = Void
  tabulateArithmetic _ = U1
  indexArithmetic U1 = absurd

instance (ArithmeticRepresentable a v, ArithmeticRepresentable a u)
  => ArithmeticRepresentable a (v :*: u) where
    type ArithmeticRep a (v :*: u) =
      Either (ArithmeticRep a v) (ArithmeticRep a u)
    tabulateArithmetic f =
      tabulateArithmetic (f . Left) :*: tabulateArithmetic (f . Right)
    indexArithmetic (a :*: _) (Left  i) = indexArithmetic a i
    indexArithmetic (_ :*: b) (Right j) = indexArithmetic b j

instance (Representable v, ArithmeticRepresentable a u)
  => ArithmeticRepresentable a (v :.: u) where
    type ArithmeticRep a (v :.: u) = (Rep v, ArithmeticRep a u)
    tabulateArithmetic =
      Comp1 . tabulate . fmap tabulateArithmetic . curry
    indexArithmetic (Comp1 fg) (i, j) = indexArithmetic (index fg i) j

mapArithmetic
  :: (ArithmeticRepresentable a u)
  => (a -> a) -> u a -> u a
mapArithmetic f = tabulateArithmetic . fmap f . indexArithmetic

pureArithmetic
  :: (ArithmeticRepresentable a u)
  => a -> u a
pureArithmetic = tabulateArithmetic . const

bindArithmetic
  :: ArithmeticRepresentable a u
  => u a -> (a -> u a) -> u a
bindArithmetic u f = tabulateArithmetic $ \a ->
  indexArithmetic (f (indexArithmetic u a)) a

zipWithArithmetic
  :: ArithmeticRepresentable a u
  => (a -> a -> a) -> u a -> u a -> u a
zipWithArithmetic f as bs = tabulateArithmetic $ \k ->
  f (indexArithmetic as k) (indexArithmetic bs k)

zipWith3Arithmetic
  :: ArithmeticRepresentable a u
  => (a -> a -> a -> a) -> u a -> u a -> u a -> u a
zipWith3Arithmetic f as bs cs = tabulateArithmetic $ \k ->
  f (indexArithmetic as k) (indexArithmetic bs k) (indexArithmetic cs k)
