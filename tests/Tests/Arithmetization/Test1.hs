{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test1 (specArithmetization1) where

import           GHC.Generics                    (Par1 (..))
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
testFunc :: forall a . Symbolic a => Par1 a -> Par1 a -> Par1 a
testFunc (Par1 x) y =
    let c  = fromConstant @Integer @a
        g1 = x ^ (2 :: Natural) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Natural)
        g3 = c 2 // x
    in (Par1 g3 == y) ? Par1 g1 $ Par1 g2

testResult :: forall a . (Symbolic a, Haskell.Eq a) => ArithmeticCircuit a -> a -> a -> Haskell.Bool
testResult r x y = acValue (applyArgs r [x, y]) Haskell.== unPar1 (testFunc @a (Par1 x) (Par1 y))

specArithmetization1 :: forall a . (Symbolic a, Arithmetic a, Arbitrary a, Show a) => Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let ac = compile @a (testFunc @(ArithmeticCircuit a)) :: ArithmeticCircuit a
            property $ \x y -> testResult ac x y
