{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Data.Combinators where

import Data.List (find)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import GHC.TypeNats (KnownNat, Natural, natVal)
import ZkFold.Base.Algebra.Basic.Class
import Prelude (Integer, div, error, mod, ($), (.))
import qualified Prelude as Haskell

maxOverflow :: forall a n. (Finite a, KnownNat n) => Natural
maxOverflow = registerSize @a @n + Haskell.ceiling (log2 $ numberOfRegisters @a @n)

highRegisterSize :: forall a n. (Finite a, KnownNat n) => Natural
highRegisterSize = getNatural @n - registerSize @a @n * (numberOfRegisters @a @n - 1)

registerSize :: forall a n. (Finite a, KnownNat n) => Natural
registerSize = Haskell.ceiling (getNatural @n % numberOfRegisters @a @n)

numberOfRegisters :: forall a n. (Finite a, KnownNat n) => Natural
numberOfRegisters =
  fromMaybe (error "too many bits, field is not big enough") $
    find (\c -> c * maxRegisterSize c Haskell.>= getNatural @n) [1 .. maxRegisterCount]
  where
    maxRegisterCount = 2 ^ bitLimit
    bitLimit = Haskell.floor $ log2 (order @a)
    maxRegisterSize regCount =
      let maxAdded = Haskell.ceiling $ log2 regCount
       in Haskell.floor $ (bitLimit - maxAdded) % (2 :: Integer)

log2 :: Natural -> Haskell.Double
log2 = Haskell.logBase 2 . Haskell.fromIntegral

getNatural :: forall n. (KnownNat n) => Natural
getNatural = natVal (Proxy :: Proxy n)

-- | The maximum number of bits a Field element can encode.
maxBitsPerFieldElement :: forall p. (Finite p) => Natural
maxBitsPerFieldElement = Haskell.floor $ log2 (order @p)

-- | The maximum number of bits it makes sense to encode in a register.
-- That is, if the field elements can encode more bits than required, choose the smaller number.
maxBitsPerRegister :: forall p n. (Finite p, KnownNat n) => Natural
maxBitsPerRegister = Haskell.min (maxBitsPerFieldElement @p) (getNatural @n)

-- | The number of bits remaining for the higher register
-- assuming that all smaller registers have the same optimal number of bits.
highRegisterBits :: forall p n. (Finite p, KnownNat n) => Natural
highRegisterBits = case getNatural @n `mod` maxBitsPerFieldElement @p of
  0 -> maxBitsPerFieldElement @p
  m -> m

-- | The lowest possible number of registers to encode @n@ bits using Field elements from @p@
-- assuming that each register storest the largest possible number of bits.
minNumberOfRegisters :: forall p n. (Finite p, KnownNat n) => Natural
minNumberOfRegisters = (getNatural @n + maxBitsPerRegister @p @n - 1) `div` maxBitsPerRegister @p @n
