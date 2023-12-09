{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test1 (specArithmetization1) where

import           Data.Bifunctor                   (bimap)
import           Prelude                          hiding (Num(..), Eq(..), Bool, (^), (>), (/), (||), not, replicate)
import qualified Prelude                          as Haskell
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Symbolic.Arithmetization  (acValue, applyArgs)
import           ZkFold.Symbolic.Compiler         (compile)
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Conditional (Conditional(..))
import           ZkFold.Symbolic.Data.Eq          (Eq (..))
import           ZkFold.Symbolic.Types            (SmallField, I, R, Symbolic)

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a . Symbolic a => a -> a -> a
testFunc x y =
    let c  = fromConstant @I @a
        g1 = x ^ (2 :: I) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: I)
        g3 = c 2 / x
    in (g3 == y :: Bool a) ? g1 $ g2

testResult :: R -> Zp SmallField -> Zp SmallField -> Haskell.Bool
testResult r x y = acValue (applyArgs r [x, y]) == testFunc @(Zp SmallField) x y

specArithmetization1 :: Spec
specArithmetization1 = do
    describe "Arithmetization test 1" $ do
        it "should pass" $ do
            let r = compile @(Zp SmallField) (testFunc @R)
            all (uncurry $ testResult r) $ zipWith (curry (bimap toZp toZp)) [0..order @SmallField - 1] [0..order @SmallField - 1]