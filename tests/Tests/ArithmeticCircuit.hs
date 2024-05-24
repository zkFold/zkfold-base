{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.ArithmeticCircuit (eval', it, specArithmeticCircuit) where

import           Data.Bool                                              (bool)
import           Data.Map                                               (empty)
import           Prelude                                                (IO, Show, String, flip, head, id, map, ($))
import qualified Prelude                                                as Haskell
import qualified Test.Hspec
import           Test.Hspec                                             (Spec, describe, hspec)
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (embed)
import           ZkFold.Symbolic.Data.Bool

eval' :: ArithmeticCircuit a -> a
eval' = flip eval empty

correctHom0 :: forall a . (Arithmetic a, FromConstant a a, Scale a a, Show a) => (forall b . Field b => b) -> Property
correctHom0 f = let r = f in withMaxSuccess 1 $ checkClosedCircuit r .&&. eval' r === f @a

correctHom1 :: forall a . (Arithmetic a, FromConstant a a, Scale a a, Show a) => (forall b . Field b => b -> b) -> a -> Property
correctHom1 f x = let r = f (embed x) in checkClosedCircuit r .&&. eval' r === f x

correctHom2 :: forall a . (Arithmetic a, FromConstant a a, Scale a a, Show a) => (forall b . Field b => b -> b -> b) -> a -> a -> Property
correctHom2 f x y = let r = f (embed x) (embed y) in checkClosedCircuit r .&&. eval' r === f x y

it :: Testable prop => String -> prop -> Spec
it desc prop = Test.Hspec.it desc (property prop)

specArithmeticCircuit :: forall a . (Arbitrary a, Arithmetic a, FromConstant a a, Scale a a, Show a) => IO ()
specArithmeticCircuit = hspec $ do
    describe "ArithmeticCircuit specification" $ do
        it "embeds constants" $ correctHom1 @a id
        it "adds correctly" $ correctHom2 @a (+)
        it "has zero" $ correctHom0 @a zero
        it "negates correctly" $ correctHom1 @a negate
        it "multiplies correctly" $ correctHom2 @a (*)
        it "has one" $ correctHom0 @a one
        it "inverts nonzero correctly" $ correctHom1 @a finv
        it "inverts zero correctly" $ correctHom0 @a (finv zero)
        it "checks isZero(nonzero)" $ \(x :: a) ->
          let Bool (r :: ArithmeticCircuit a) = isZero (embed x)
           in checkClosedCircuit r .&&. eval' r === bool zero one (x Haskell.== zero)
        it "checks isZero(0)" $
          let Bool (r :: ArithmeticCircuit a) = isZero (zero :: ArithmeticCircuit a)
           in withMaxSuccess 1 $ checkClosedCircuit r .&&. eval' r === one
        it "computes binary expansion" $ withMaxSuccess 10 $ \(x :: a) ->
          let rs = binaryExpansion (embed x)
           in checkClosedCircuit (head rs) .&&. map eval' rs === padBits (numberOfBits @a) (binaryExpansion x)
        it "internalizes equality" $ \(x :: a) (y :: a) ->
          let Bool (r :: ArithmeticCircuit a) = embed x == embed y
           in checkClosedCircuit r .&&. eval' r === bool zero one (x Haskell.== y)
        it "internal equality is reflexive" $ \(x :: a) ->
          let Bool (r :: ArithmeticCircuit a) = embed x == embed x
           in checkClosedCircuit r .&&. eval' r === one
