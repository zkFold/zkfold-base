{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test1 (specArithmetization1) where

import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (Bool, Eq (..), Num (..), not, replicate, (/), (>), (^), (||))
import qualified Prelude                          as Haskell
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import qualified ZkFold.Base.Data.Vector          as V
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Conditional (Conditional (..))
import           ZkFold.Symbolic.Data.Eq          (Eq (..))
import           ZkFold.Symbolic.Types            (I, Symbolic)

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a . Symbolic a => a -> a -> a
testFunc x y =
    let c  = fromConstant @I @a
        g1 = x ^ (2 :: Natural) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Natural)
        g3 = c 2 // x
    in (g3 == y :: Bool a) ? g1 $ g2

testResult :: forall a . (Symbolic a, Haskell.Eq a) => ArithmeticCircuit 1 a -> a -> a -> Haskell.Bool
testResult r x y = V.item (acValue (applyArgs r [x, y])) Haskell.== testFunc @a x y

specArithmetization1 :: forall a . (Symbolic a, Arithmetic a, Arbitrary a, Show a) => Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let ac = compile @a (testFunc @(ArithmeticCircuit 1 a)) :: ArithmeticCircuit 1 a
            property $ \x y -> testResult ac x y
