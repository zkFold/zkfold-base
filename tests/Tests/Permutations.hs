{-# LANGUAGE TypeApplications #-}

module Tests.Permutations (specPermutations) where

import           Data.List                              (sort)
import           Data.Map                               (elems)
import           Prelude                                hiding (Num(..), Fractional(..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Permutations
import           ZkFold.Base.Data.Vector                (fromVector)
import           ZkFold.Prelude                         (length)

data TestSize
instance Finite TestSize where
    order = 100

specPermutations :: IO ()
specPermutations = hspec $ do
    describe "Permutations specification" $ do
        describe "Function: mkIndexPartition" $ do
            it "should preserve the total number of elements" $ property $
                \xs -> length (concat $ elems $ mkIndexPartition xs) `shouldBe` length xs
        describe "Function: fromCycles" $ do
            it "should preserve the elements" $ property $
                \v -> 
                    let ts = mkIndexPartition $ fromVector @TestSize v
                        p = fromPermutation @TestSize $ fromCycles ts
                    in sort p == sort (concat $ elems ts)