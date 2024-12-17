{-# LANGUAGE AllowAmbiguousTypes  #-}

module ZkFold.Base.Algorithm.ReedSolomon where


import GHC.Natural (Natural)
import ZkFold.Base.Algebra.Basic.Number (value, KnownNat)
import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Field (Zp)
import ZkFold.Base.Algebra.Polynomials.Univariate
import Prelude (iterate, ($), Foldable (foldl), Eq)
import ZkFold.Prelude (take)
import Data.Vector (fromList)


type RSField p = Zp p

data RSParams c i j = ReedSolomonParams
    { fullLength      :: Natural
    , usefulLength    :: Natural
    , bitsPerBlock    :: Natural
    }

numberOfError :: forall n k. (KnownNat n, KnownNat k) => Natural
numberOfError = (value @n -! value @k) `div` 2

generator :: forall n k a. (KnownNat n, KnownNat k, Field a, Eq a) => a -> Poly a
generator a = foldl (\pi ai -> pi * toLinPoly ai) one roots
    where
        dif = value @n -! value @k
        roots = take dif $ iterate (* a) a
        toLinPoly p = toPoly $ fromList [one, negate p]
