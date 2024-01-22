module ZkFold.Base.Algebra.Basic.Permutations where

import           Data.Map                         (Map, empty, union, elems, singleton)
import           Prelude                          hiding (Num(..), (!!), length)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                   ((!!), length, elemIndex)

-- TODO (Issue #18): make the code safer

type IndexSet = [Integer]
type IndexPartition = Map Integer IndexSet

mkIndexPartition :: [Integer] -> IndexPartition
mkIndexPartition vs =
    let f = \i -> singleton i $ map snd $ filter (\(v, _) -> v == i) $ zip vs [1 .. length vs]
    in foldl union empty $ map f vs

newtype Permutation = Permutation [Integer]

applyCycle :: IndexSet -> Permutation -> Permutation
applyCycle c (Permutation perm) = Permutation $ map f perm
    where
        f :: Integer -> Integer
        f i = case i `elemIndex` c of
            Just j  -> c !! ((j + 1) `mod` length c)
            Nothing -> i

fromCycles :: IndexPartition -> Permutation
fromCycles p =
    let n = length $ concat $ elems p
    in foldr applyCycle (Permutation [1 .. n]) $ elems p