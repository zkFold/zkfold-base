{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Tests.Symbolic.ArithmeticCircuit (exec1, it, specArithmeticCircuit) where

import           Data.Binary                                 (Binary)
import           Data.Bool                                   (bool)
import           Data.Functor                                ((<$>))
import           Data.Functor.Rep                            (Representable (..))
import           GHC.Generics                                (Par1, U1 (..))
import           Prelude                                     (Foldable, Ord, Show, String, id, return, ($))
import qualified Prelude                                     as Haskell
import qualified Test.Hspec
import           Test.Hspec                                  (Spec, describe)
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.Data.Ord                    ((<=))

correctHom0 ::
  forall a. (Arithmetic a, Binary a, Show a) =>
  (forall b . Field b => b) -> Property
correctHom0 f = let r = fromFieldElement f in withMaxSuccess 1 $ checkClosedCircuit r .&&. exec1 r === f @a

correctHom1 ::
  (Arithmetic a, Binary a, Show a) =>
  (forall b . Field b => b -> b) -> a -> Property
correctHom1 f x = let r = fromFieldElement $ f (fromConstant x) in checkClosedCircuit r .&&. exec1 r === f x

correctHom2 ::
  (Arithmetic a, Binary a, Show a) =>
  (forall b . Field b => b -> b -> b) -> a -> a -> Property
correctHom2 f x y = let r = fromFieldElement $ f (fromConstant x) (fromConstant y)
                    in checkClosedCircuit r .&&. exec1 r === f x y

instance Arbitrary (U1 a) where
  arbitrary = return U1

propCircuitInvariance ::
  ( Arithmetic a, Binary a, Show a, Ord (Rep i)
  , Representable p, Representable i, Foldable i) =>
  ArithmeticCircuit a p i Par1 -> p a -> i a -> Property
propCircuitInvariance ac pl wi = eval ac pl wi === eval (mapVarArithmeticCircuit ac) pl wi

it :: Testable prop => String -> prop -> Spec
it desc prop = Test.Hspec.it desc (property prop)

specArithmeticCircuit' :: forall a . (Arbitrary a, Arithmetic a, Binary a, Show a) => Spec
specArithmeticCircuit' = do
    describe "ArithmeticCircuit specification" $ do
        it "embeds constants" $ correctHom1 @a id
        it "adds correctly" $ correctHom2 @a (+)
        it "has zero" $ correctHom0 @a zero
        it "negates correctly" $ correctHom1 @a negate
        it "multiplies correctly" $ correctHom2 @a (*)
        it "has one" $ correctHom0 @a one
        it "inverts nonzero correctly" $ correctHom1 @a finv
        it "inverts zero correctly" $ correctHom0 @a (finv zero)
        -- it "checks isZero(nonzero)" $ \(x :: a) ->
        --   let Bool (r :: ArithmeticCircuit a U1 Par1) = isZero $ FieldElement (embed x)
        --    in checkClosedCircuit r .&&. exec1 r === bool zero one (x Haskell.== zero)
        -- it "checks isZero(0)" $
        --   let Bool (r :: ArithmeticCircuit a U1 Par1) = isZero (zero :: FieldElement (ArithmeticCircuit a U1))
        --    in withMaxSuccess 1 $ checkClosedCircuit r .&&. exec1 r === one
        it "computes binary expansion" $ \(x :: a) ->
          let rs = binaryExpansion (fromConstant x :: FieldElement (ArithmeticCircuit a U1 U1))
              as = padBits (numberOfBits @a) $ fromConstant <$> binaryExpansion (toConstant x)
           in checkClosedCircuit rs .&&. V.fromVector (exec rs) === as
        it "internalizes equality" $ \(x :: a) (y :: a) ->
          let Bool r = (fromConstant x :: FieldElement (ArithmeticCircuit a U1 U1)) == fromConstant y
           in checkClosedCircuit @a r .&&. exec1 r === bool zero one (x Haskell.== y)
        it "internal equality is reflexive" $ \(x :: a) ->
          let Bool r = (fromConstant x :: FieldElement (ArithmeticCircuit a U1 U1)) == fromConstant x
           in checkClosedCircuit @a r .&&. exec1 r === one
        it "<=s correctly" $ withMaxSuccess 10 $ \(x :: a) (y :: a) ->
          let Bool r = (fromConstant x :: FieldElement (ArithmeticCircuit a U1 U1)) <= fromConstant y
           in checkClosedCircuit @a r .&&. exec1 r === bool zero one (x Haskell.<= y)
        describe "Variable mapping" $ do
            it "does not change the circuit" $ propCircuitInvariance @a @(Vector 2) @U1

specArithmeticCircuit :: Spec
specArithmeticCircuit = do
  specArithmeticCircuit' @(Zp BLS12_381_Scalar)
