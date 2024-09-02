{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           GHC.Generics                                (Par1 (unPar1))
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), (==>))

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..), one, zero)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (..))
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), compile, eval)
import           ZkFold.Symbolic.Data.Bool                   (Bool (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

type C = BLS12_381_G1
type F = ScalarField C

lockedByTxId :: forall a c . (FromConstant a (FieldElement c), Symbolic c) => a -> FieldElement c -> Bool c
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: F -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))
        b       = unPar1 (eval ac (V.singleton targetValue))
    in b Haskell.== one

testDifferentValue :: F -> F -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))
        b       = unPar1 (eval ac (V.singleton otherValue))
    in b Haskell.== zero

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x Haskell./= y ==> testDifferentValue x y
