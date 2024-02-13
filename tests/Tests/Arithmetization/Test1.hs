{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test1 (specArithmetization1) where

import           Prelude                          hiding (Num(..), Eq(..), Bool, (^), (>), (/), (||), not, replicate)
import qualified Prelude                          as Haskell
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Conditional (Conditional(..))
import           ZkFold.Symbolic.Data.Eq          (Eq (..))
import           ZkFold.Symbolic.Types            (I, Symbolic)

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a . Symbolic a => a -> a -> a
testFunc x y =
    let c  = fromConstant @I @a
        g1 = x ^ (2 :: I) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: I)
        g3 = c 2 / x
    in (g3 == y :: Bool a) ? g1 $ g2

testResult :: forall a . (Symbolic a, Haskell.Eq a) => ArithmeticCircuit a -> a -> a -> Haskell.Bool
testResult r x y = acValue (applyArgs r [x, y]) == testFunc @a x y

specArithmetization1 :: forall a . (Symbolic a, Arithmetic a, Arbitrary a, Show a) => Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let ac = compile @a (testFunc @(ArithmeticCircuit a)) :: ArithmeticCircuit a
            property $ \x y -> testResult ac x y
