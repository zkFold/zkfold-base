module ZkFold.Base.Data.PartialOrder where

import           Data.List (intersect, nub)
import           Data.Map  (Map, elems, fromList)
import           Prelude

mergeOrderedLists :: Eq a => [a] -> [a] -> [a]
mergeOrderedLists xs ys = mergeOrderedLists' xs' ys' zs
    where
        xs' = nub xs
        ys' = nub ys
        zs = xs' `intersect` ys'

mergeOrderedLists' :: Eq a => [a] -> [a] -> [a] -> [a]
mergeOrderedLists' xs ys [] = xs ++ ys
mergeOrderedLists' xs ys (z:zs) =
    takeWhile (/= z) xs ++ takeWhile (/= z) ys ++ [z] ++
    mergeOrderedLists' (dropWhile (== z) $ dropWhile (/= z) xs) (dropWhile (== z) $ dropWhile (/= z) ys) zs

mergeMaps :: Eq a => Map Integer a -> Map Integer a -> Map Integer a
mergeMaps xs ys = fromList $ zip [0..] $ mergeOrderedLists (elems xs) (elems ys)