{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Basic.Permutations where

import           Prelude                                     hiding (Num(..), (^), (/), (!!), sum, length, take, drop)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                             ((!!), length)

newtype IndexSet a = IndexSet [Integer]
newtype IndexPartition a = IndexPartition [IndexSet a]

newtype Permutation a = Permutation [Integer]

applyCycle :: IndexSet a -> Permutation a -> Permutation a
applyCycle (IndexSet c) (Permutation perm) =
    let f = \i -> if i `elem` c then c !! (i + 1) `mod` length c else i
    in Permutation $ map f perm

fromCycles :: forall a . Finite a => IndexPartition a -> Permutation a
fromCycles (IndexPartition cs) = foldr applyCycle (Permutation [0 .. order @a -1]) cs