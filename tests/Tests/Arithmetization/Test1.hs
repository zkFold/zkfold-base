{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test1 (specArithmetization1) where

import           Data.Functor.Identity           (Identity (..))
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Bool, Eq (..), Num (..), not, replicate, (/), (>), (^), (||))
import qualified Prelude                         as Haskell
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Types           (Symbolic)

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a . Symbolic a => Identity a -> Identity a -> Identity a
testFunc (Identity x) y =
    let c  = fromConstant @Integer @a
        g1 = x ^ (2 :: Natural) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Natural)
        g3 = c 2 // x
    in (Identity g3 == y) ? Identity g1 $ Identity g2

testResult :: forall a . (Symbolic a, Haskell.Eq a) => ArithmeticCircuit a -> a -> a -> Haskell.Bool
testResult r x y = acValue (applyArgs r [x, y]) Haskell.== runIdentity (testFunc @a (Identity x) (Identity y))

specArithmetization1 :: forall a . (Symbolic a, Arithmetic a, Arbitrary a, Show a) => Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let ac = compile @a (testFunc @(ArithmeticCircuit a)) :: ArithmeticCircuit a
            property $ \x y -> testResult ac x y
