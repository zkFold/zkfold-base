{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test1 (specArithmetization1) where

import           GHC.Generics                      (Par1 (unPar1))
import           Numeric.Natural                   (Natural)
import           Prelude                           hiding (Bool, Eq (..), Num (..), not, replicate, (/), (>), (^), (||))
import qualified Prelude                           as Haskell
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector           (Vector, unsafeToVector)
import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool         (Bool (..))
import           ZkFold.Symbolic.Data.Conditional  ((?))
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Interpreter       (Interpreter)
import           ZkFold.Symbolic.MonadCircuit      (Arithmetic)

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall c . (Symbolic c, Field (FieldElement c)) => FieldElement c -> FieldElement c -> FieldElement c
testFunc x y =
    let c  = fromConstant @Integer @(FieldElement c)
        g1 = x ^ (2 :: Natural) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Natural)
        g3 = c 2 // x
    in (g3 == y :: Bool c) ? g1 $ g2

testResult :: forall a . (FromConstant a a, Arithmetic a) => ArithmeticCircuit a (Vector 2) Par1 -> a -> a -> Haskell.Bool
testResult r x y = fromConstant (unPar1 $ eval r (unsafeToVector [x, y])) Haskell.==
    testFunc @(Interpreter a) (fromConstant x) (fromConstant y)

specArithmetization1 :: forall a . (FromConstant a a, Arithmetic a, Arbitrary a, Show a) => Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let ac = compile @a (testFunc @(ArithmeticCircuit a (Vector 2))) :: ArithmeticCircuit a (Vector 2) Par1
            property $ \x y -> testResult ac x y
