{-# LANGUAGE TypeApplications #-}

module Tests.Permutations (specPermutations) where

import           Data.List                              (sort)
import           Data.Map                               (elems)
import qualified Data.Vector                            as V
import           Prelude                                hiding (Fractional (..), Num (..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Permutations
import           ZkFold.Base.Data.Vector                (fromVector)

data TestSize
instance Finite TestSize where
    order = 100

specPermutations :: IO ()
specPermutations = hspec $ do
    describe "Permutations specification" $ do
        describe "Function: mkIndexPartition" $ do
            it "should preserve the total number of elements" $ property $
                \xsL -> let xs = V.fromList xsL in V.length (V.concat $ elems $ mkIndexPartition @Integer xs) `shouldBe` V.length xs
        describe "Function: fromCycles" $ do
            it "should preserve the elements" $ property $
                \v ->
                    let ts = mkIndexPartition @Integer $ V.fromList $ fromVector @TestSize v
                        p = fromPermutation @TestSize $ fromCycles $ ts
                    in sort p == sort (V.toList $ V.concat $ elems ts)

