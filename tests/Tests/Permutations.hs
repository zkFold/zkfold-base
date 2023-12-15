module Tests.Permutations (specPermutations) where

import           Data.List                              (sort)
import           Data.Map                               (elems)
import           Prelude                                hiding (Num(..), Fractional(..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Permutations
import           ZkFold.Prelude                         (length)

specPermutations :: IO ()
specPermutations = hspec $ do
    describe "Permutations specification" $ do
        describe "Function: mkIndexPartition" $ do
            it "should preserve the total number of elements" $ property $
                \xs -> length (concat $ elems $ mkIndexPartition xs) `shouldBe` length xs
        describe "Function: fromCycles" $ do
            it "should preserve the elements" $ property $
                \xs -> 
                    let ts = mkIndexPartition xs
                        Permutation p = fromCycles ts
                    in sort p == sort (concat $ elems ts)