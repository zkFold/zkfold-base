{-# LANGUAGE AllowAmbiguousTypes  #-}

module ZkFold.Base.Algorithm.ReedSolomon where


import GHC.Natural (Natural)
import ZkFold.Base.Algebra.Basic.Number (value, KnownNat)
import ZkFold.Base.Algebra.Basic.Class ((-!), div)
import ZkFold.Base.Algebra.Basic.Field (Zp)
import ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial (Poly, Polynomial)


type RSField p = Zp p

data RSParams c i j = ReedSolomonParams
    { fullLength      :: Natural
    , usefulLength    :: Natural
    , bitsPerBlock    :: Natural
    }

numberOfError :: forall n k. (KnownNat n, KnownNat k) => Natural
numberOfError = (value @n -! value @k) `div` 2

-- vecToPoly :: Polynomial c i j => [c] -> Poly c i j
-- vecToPoly v = foldl (\p -> p * )