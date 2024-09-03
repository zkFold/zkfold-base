{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Utils where

import           Data.Bifunctor                                      (first)
import           Data.Bool                                           (bool)
import           Data.Map                                            (insertWith, fromList, toList)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, replicate, (!!),
                                                                      (/), (^))
import           System.Random                                       (RandomGen, mkStdGen, uniformR)
import           Test.QuickCheck                                     (Gen, shuffle)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Prelude                                      (log2ceiling, take, replicate)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

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

genVarSet :: (KnownNat i, Arithmetic a) => Natural -> ArithmeticCircuit a (Vector i) f -> Gen [Var (Vector i)]
genVarSet l ac = take l <$> shuffle (getAllVars ac)

sortByList :: Ord a => [a] -> [a] -> [a]
sortByList f t =
    let m  = fromList $ zip t (repeat @Natural 0)
        m' = foldl (\acc x -> insertWith (+) x 1 acc) m f
    in concatMap (\(k, v) -> replicate v k) $ toList m'