{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Basic.Permutations (
    IndexSet,
    IndexPartition,
    Permutation,
    fromPermutation,
    applyPermutation,
    mkIndexPartition,
    fromCycles
) where

import           Data.Map                         (Map, empty, union, elems, singleton)
import           Data.Maybe                       (fromJust)
import           Prelude                          hiding (Num(..), (!!), length, drop)
import           Test.QuickCheck                  (Arbitrary (..), choose)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector          (Vector(..), toVector, fromVector)
import           ZkFold.Prelude                   ((!!), length, elemIndex, drop)

-- TODO (Issue #18): make the code safer

------------------------------ Index sets and partitions -------------------------------------

type IndexSet = [Integer]
type IndexPartition = Map Integer IndexSet

mkIndexPartition :: [Integer] -> IndexPartition
mkIndexPartition vs =
    let f i = singleton i $ map snd $ filter (\(v, _) -> v == i) $ zip vs [1 .. length vs]
    in foldl union empty $ map f vs

------------------------------------- Permutations -------------------------------------------

newtype Permutation n = Permutation (Vector n Integer)
    deriving (Show, Eq)

instance Finite n => Arbitrary (Permutation n) where
    arbitrary =
        let f as [] = return as
            f as bs = do
                i <- choose (0, length bs - 1)
                let as' = (bs !! i) : as
                    bs' = drop i bs
                f as' bs'
        in Permutation . Vector <$> f [] [1..order @n]

fromPermutation :: Permutation n -> [Integer]
fromPermutation (Permutation perm) = fromVector perm

applyPermutation :: Permutation n -> Vector n a -> Vector n a
applyPermutation (Permutation (Vector ps)) (Vector as) = Vector $ map (as !!) ps

applyCycle :: IndexSet -> Permutation n -> Permutation n
applyCycle c (Permutation perm) = Permutation $ fmap f perm
    where
        f :: Integer -> Integer
        f i = case i `elemIndex` c of
            Just j  -> c !! ((j + 1) `mod` length c)
            Nothing -> i

fromCycles :: Finite n => IndexPartition -> Permutation n
fromCycles p =
    let n = length $ concat $ elems p
    in foldr applyCycle (Permutation $ fromJust $ toVector [1 .. n]) $ elems p