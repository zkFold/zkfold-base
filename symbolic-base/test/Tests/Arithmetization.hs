{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Tests.Arithmetization (specArithmetization) where

import           Control.DeepSeq                             (NFData)
import           Data.Binary                                 (Binary)
import           Data.Functor.Rep                            (Representable (..))
import           GHC.Generics                                (Par1, U1 (..))
import           Prelude
import           Test.Hspec
import           Test.QuickCheck
import           Tests.Arithmetization.Optimization          (specOptimization)
import           Tests.Arithmetization.Test1                 (specArithmetization1)
import           Tests.Arithmetization.Test2                 (specArithmetization2)
import           Tests.Arithmetization.Test3                 (specArithmetization3)
import           Tests.Arithmetization.Test4                 (specArithmetization4)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Class                       (Arithmetic)
import           ZkFold.Symbolic.Compiler

propCircuitInvariance ::
  ( Arithmetic a, Binary a, Show a, Ord (Rep i)
  , Representable p, Representable i, Foldable i) =>
  ArithmeticCircuit a p i Par1 -> p a -> i a -> Property
propCircuitInvariance ac pl wi = eval ac pl wi === eval (mapVarArithmeticCircuit ac) pl wi

specArithmetization' ::
  forall a p i .
  (Arithmetic a, Arbitrary a, Binary a, Binary (Rep p)) =>
  (Arbitrary (p a), Arbitrary (i a)) =>
  (Show a, Show (p a), Show (i a), Show (ArithmeticCircuit a p i Par1)) =>
  (Arbitrary (Rep i), Binary (Rep i), Ord (Rep i), NFData (Rep i)) =>
  (Representable p, Representable i, Traversable i) => IO ()
specArithmetization' = hspec $ do
    describe "Arithmetization specification" $ do
        describe "Variable mapping" $ do
            it "does not change the circuit" $ property $ propCircuitInvariance @a @i @p
        specArithmetization1 @a
        specArithmetization2
        specArithmetization3
        specArithmetization4

instance Arbitrary (U1 a) where
  arbitrary = return U1

specArithmetization :: IO ()
specArithmetization = do
    specArithmetization' @(Zp BLS12_381_Scalar) @U1 @(Vector 2)
    specOptimization @(Zp BLS12_381_Scalar)
