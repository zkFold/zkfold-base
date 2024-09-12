{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Utils where

import           Data.Bifunctor                   (first)
import           Data.Bool                        (bool)
import           Data.Map                         (fromList, insertWith, toList)
import           Prelude                          hiding (Num (..), drop, length, replicate, sum, take, (!!), (/), (^))
import           System.Random                    (RandomGen, mkStdGen, uniformR)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                   (log2ceiling, replicate)

getParams :: forall a . (Eq a, FiniteField a) => Natural -> (a, a, a)
getParams n = findK' $ mkStdGen 0
    where
        omega = case rootOfUnity @a (log2ceiling n) of
                  Just o -> o
                  _      -> error "impossible"
        hGroup = map (omega^) [0 .. n-!1]
        hGroup' k = map (k*) hGroup

        findK' :: RandomGen g => g -> (a, a, a)
        findK' g =
            let (k1, g') = first fromConstant $ uniformR (1, order @a -! 1) g
                (k2, g'') = first fromConstant $ uniformR (1, order @a -! 1) g'
            in bool (findK' g'') (omega, k1, k2) $
                all (`notElem` hGroup) (hGroup' k1)
                && all (`notElem` hGroup' k1) (hGroup' k2)

sortByList :: Ord a => [a] -> [a] -> [a]
sortByList f t =
    let m  = fromList $ zip t (repeat @Natural 0)
        m' = foldl (\acc x -> insertWith (+) x 1 acc) m f
    in concatMap (\(k, v) -> replicate v k) $ toList m'
