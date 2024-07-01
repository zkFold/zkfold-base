module ZkFold.Base.Protocol.ARK.Plonk.Internal where

import           Data.Bifunctor                  (first)
import           Data.Bool                       (bool)
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           System.Random                   (RandomGen, mkStdGen, uniformR)

import           ZkFold.Base.Algebra.Basic.Class

getParams :: forall a . (Eq a, FiniteField a) => Natural -> (a, a, a)
getParams l = findK' $ mkStdGen 0
    where
        omega = case rootOfUnity @a l of
                  Just o -> o
                  _      -> error "impossible"
        hGroup = map (omega^) [1 .. 2^l-!1]
        hGroup' k = map (k*) hGroup

        findK' :: RandomGen g => g -> (a, a, a)
        findK' g =
            let (k1, g') = first fromConstant $ uniformR (1, order @a -! 1) g
                (k2, g'') = first fromConstant $ uniformR (1, order @a -! 1) g'
            in bool (findK' g'') (omega, k1, k2) $
                all (`notElem` hGroup) (hGroup' k1)
                && all (`notElem` hGroup' k1) (hGroup' k2)
