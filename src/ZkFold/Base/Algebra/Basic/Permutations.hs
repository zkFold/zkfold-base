{-# LANGUAGE OverloadedLists  #-}
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

import           Data.Functor.Rep                 (Representable (index))
import           Data.Map                         (Map, elems, empty, singleton, union)
import           Data.Maybe                       (fromJust)
import qualified Data.Vector                      as V
import           Prelude                          hiding (Num (..), drop, length, mod, (!!))
import qualified Prelude                          as P
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector          (Vector (..), fromVector, toVector, unsafeToVector)
import           ZkFold.Prelude                   (chooseNatural, drop, length, (!!))

-- TODO (Issue #18): make the code safer

------------------------------ Index sets and partitions -------------------------------------

type IndexSet = V.Vector Natural
type IndexPartition a = Map a IndexSet

mkIndexPartition :: Ord a => V.Vector a -> IndexPartition a
mkIndexPartition vs =
    let f i = singleton i $ fmap snd $ V.filter (\(v, _) -> v == i) $ V.zip vs [0 .. length vs P.- 1]
    in V.foldl union empty $ fmap f vs

------------------------------------- Permutations -------------------------------------------

newtype Permutation n = Permutation (Vector n (Zp n))
    deriving (Show, Eq)

instance KnownNat n => Arbitrary (Permutation n) where
    arbitrary =
        let f as [] = return as
            f as bs = do
                i <- chooseNatural (0, length bs -! 1)
                let as' = (bs !! i) : as
                    bs' = drop i bs
                f as' bs'
        in Permutation . unsafeToVector <$>
              f [] [fromConstant x | x <- [1..value @n]]

fromPermutation :: Permutation n -> [Zp n]
fromPermutation (Permutation perm) = fromVector perm

applyPermutation :: KnownNat n => Permutation n -> Vector n a -> Vector n a
applyPermutation (Permutation ps) as = fmap (index as) ps

applyCycle :: KnownNat n => V.Vector Natural -> Permutation n -> Permutation n
applyCycle c (Permutation perm) = Permutation $ fmap (fromConstant . f . toConstant) perm
    where
        f :: Natural -> Natural
        f i = case i `V.elemIndex` c of
            Just j  -> c V.! ((j P.+ 1) `P.mod` V.length c)
            Nothing -> i

fromCycles :: KnownNat n => IndexPartition a -> Permutation n
fromCycles p =
    let n = toInteger $ V.length $ V.concat $ elems p
    in foldr applyCycle (Permutation $ fromJust $ toVector [fromConstant x | x <- [0 .. n P.- 1]]) $ elems p

