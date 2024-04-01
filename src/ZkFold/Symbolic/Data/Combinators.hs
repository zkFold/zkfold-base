{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.Combinators where

import           Data.List                       (find)
import           Data.Maybe                      (fromMaybe)
import           Data.Proxy                      (Proxy (..))
import           Data.Ratio                      ((%))
import           GHC.TypeNats                    (KnownNat, Natural, natVal)
import           Prelude                         (Integer, error, ($), (.))
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class

maxOverflow :: forall a n . (Finite a, KnownNat n) => Natural
maxOverflow = registerSize @a @n + Haskell.ceiling (log2 $ numberOfRegisters @a @n)

highRegisterSize :: forall a n . (Finite a, KnownNat n) => Natural
highRegisterSize = getNatural @n - registerSize @a @n * (numberOfRegisters @a @n - 1)

registerSize :: forall a n . (Finite a, KnownNat n) => Natural
registerSize = Haskell.ceiling (getNatural @n % numberOfRegisters @a @n)

numberOfRegisters :: forall a n . (Finite a, KnownNat n) => Natural
numberOfRegisters = fromMaybe (error "too many bits, field is not big enough")
    $ find (\c -> c * maxRegisterSize c Haskell.>= getNatural @n) [1 .. maxRegisterCount]
    where
        maxRegisterCount = 2 ^ bitLimit
        bitLimit = Haskell.floor $ log2 (order @a)
        maxRegisterSize regCount =
            let maxAdded = Haskell.ceiling $ log2 regCount
             in Haskell.floor $ (bitLimit - maxAdded) % (2 :: Integer)

log2 :: Natural -> Haskell.Double
log2 = Haskell.logBase 2 . Haskell.fromIntegral

getNatural :: forall n . KnownNat n => Natural
getNatural = natVal (Proxy :: Proxy n)
