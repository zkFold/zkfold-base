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
import           ZkFold.Symbolic.Interpreter      (Interpreter (Interpreter))

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall b . (Field (b 1), Eq (Bool b) (b 1), Conditional (Bool b) (b 1)) => b 1 -> b 1 -> b 1
testFunc x y =
    let c  = fromConstant @Integer @(b 1)
        g1 = x ^ (2 :: Natural) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Natural)
        g3 = c 2 // x
    in (g3 == y :: Bool b) ? g1 $ g2

testResult :: forall a . Arithmetic a => ArithmeticCircuit a 1 -> a -> a -> Haskell.Bool
testResult r x y = Interpreter (acValue (applyArgs r [x, y])) Haskell.==
    testFunc @(Interpreter a) (Interpreter (V.singleton x)) (Interpreter (V.singleton x))

specArithmetization1 :: forall a . (Arithmetic a, Arbitrary a, Show a) => Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let ac = compile @a (testFunc @(ArithmeticCircuit a)) :: ArithmeticCircuit a 1
            property $ \x y -> testResult ac x y
