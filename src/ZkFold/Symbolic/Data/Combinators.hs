{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ZkFold.Symbolic.Data.Combinators where

import           Control.Monad                                             (mapM)
import           Data.Kind                                                 (Type)
import           Data.List                                                 (find, splitAt)
import           Data.List.Split                                           (chunksOf)
import           Data.Maybe                                                (fromMaybe)
import           Data.Proxy                                                (Proxy (..))
import           Data.Ratio                                                ((%))
import           Data.Type.Bool                                            (If)
import           Data.Type.Ord
import           GHC.TypeNats
import           Prelude                                                   (error, head, pure, tail, ($), (.), (<$>),
                                                                            (<>))
import qualified Prelude                                                   as Haskell
import           Type.Errors

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                          (value)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, horner)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint

-- | A class for isomorphic types.
-- The @Iso b a@ context ensures that transformations in both directions are defined
--
class Iso b a => Iso a b where
    from :: a -> b

-- | Describes types that can increase their capacity by adding zero bits to the beginning (i.e. before the higher register).
--
class Extend a b where
    extend :: a -> b

-- | Describes types that can shrink their capacity by removing higher bits.
--
class Shrink a b where
    shrink :: a -> b



-- | Convert an @ArithmeticCircuit@ to bits and return their corresponding variables.
--
toBits
    :: forall i a m
    .  MonadBlueprint i a m
    => [i]
    -> Natural
    -> Natural
    -> m [i]
toBits regs hiBits loBits = do
    let lows = tail regs
        high = head regs

    bitsLow  <- Haskell.concatMap Haskell.reverse <$> mapM (expansion loBits) lows
    bitsHigh <- Haskell.reverse <$> expansion hiBits high

    pure $ bitsHigh <> bitsLow


-- | The inverse of @toBits@.
--
fromBits
    :: forall a
    .  Natural
    -> Natural
    -> (forall i m. MonadBlueprint i a m => [i] -> m [i])
fromBits hiBits loBits bits = do
    let (bitsHighNew, bitsLowNew) = splitAt (Haskell.fromIntegral hiBits) bits
    let lowVarsNew = chunksOf (Haskell.fromIntegral loBits) bitsLowNew

    lowsNew <- mapM (horner . Haskell.reverse) lowVarsNew
    highNew <- horner . Haskell.reverse $  bitsHighNew

    pure $ highNew : lowsNew

data RegisterSize = Auto | Fixed Natural

class KnownRegisterSize (r :: RegisterSize) where
  regSize :: RegisterSize

instance KnownRegisterSize Auto where
  regSize = Auto

instance KnownNat n => KnownRegisterSize (Fixed n) where
  regSize = Fixed (value @n)

maxOverflow :: forall a n r . (Finite a, KnownNat n, KnownRegisterSize r) => Natural
maxOverflow = registerSize @a @n @r + Haskell.ceiling (log2 $ numberOfRegisters @a @n @r)

highRegisterSize :: forall a n r . (Finite a, KnownNat n, KnownRegisterSize r) => Natural
highRegisterSize = getNatural @n -! registerSize @a @n @r * (numberOfRegisters @a @n @r -! 1)

registerSize  :: forall a n r. (Finite a, KnownNat n, KnownRegisterSize r) => Natural
registerSize = case regSize @r of
    Auto     -> Haskell.ceiling (getNatural @n % numberOfRegisters @a @n @r)
    Fixed rs -> rs

type family NumberOfRegisters (a :: Type) (bits :: Natural) (r :: RegisterSize ) :: Natural where
  NumberOfRegisters a bits (Fixed rs) = If (Mod bits rs >? 0 ) (Div bits rs + 1) (Div bits rs) -- if rs <= maxregsize a, ceil (n / rs)
  NumberOfRegisters a bits Auto       = NumberOfRegisters' a bits (ListRange 1 50) -- TODO: Compilation takes ages if this constant is greater than 10000.
                                                                          -- But it is weird anyway if someone is trying to store a value
                                                                          -- which requires more than 50 registers.

type family NumberOfRegisters' (a :: Type) (bits :: Natural) (c :: [Natural]) :: Natural where
    NumberOfRegisters' a bits '[] = 0
    NumberOfRegisters' a bits (x ': xs) =
        OrdCond (CmpNat bits (x * MaxRegisterSize a x))
            x
            x
            (NumberOfRegisters' a bits xs)

type family BitLimit (a :: Type) :: Natural where
    BitLimit a = Log2 (Order a)

type family MaxAdded (regCount :: Natural) :: Natural where
    MaxAdded regCount =
        OrdCond (CmpNat regCount (2 ^ Log2 regCount))
            (TypeError (Text "Impossible"))
            (Log2 regCount)
            (1 + Log2 regCount)

type family MaxRegisterSize (a :: Type) (regCount :: Natural) :: Natural where
    MaxRegisterSize a regCount = Div (BitLimit a - MaxAdded regCount) 2

type family ListRange (from :: Natural) (to :: Natural) :: [Natural] where
    ListRange from from = '[from]
    ListRange from to = from ': (ListRange (from + 1) to)



numberOfRegisters :: forall a n r . ( Finite a, KnownNat n, KnownRegisterSize r) => Natural
numberOfRegisters =  case regSize @r of
    Auto -> fromMaybe (error "too many bits, field is not big enough")
        $ find (\c -> c * maxRegisterSize c Haskell.>= getNatural @n) [1 .. maxRegisterCount]
        where
            maxRegisterCount = 2 ^ bitLimit
            bitLimit = Haskell.floor $ log2 (order @a)
            maxRegisterSize regCount =
                let maxAdded = Haskell.ceiling $ log2 regCount
                in Haskell.floor $ (bitLimit -! maxAdded) % 2
    Fixed rs -> Haskell.ceiling (value @n % rs)

log2 :: Natural -> Haskell.Double
log2 = Haskell.logBase 2 . Haskell.fromIntegral

getNatural :: forall n . KnownNat n => Natural
getNatural = natVal (Proxy :: Proxy n)

-- | The maximum number of bits a Field element can encode.
--
maxBitsPerFieldElement :: forall p. Finite p => Natural
maxBitsPerFieldElement = Haskell.floor $ log2 (order @p)

-- | The maximum number of bits it makes sense to encode in a register.
-- That is, if the field elements can encode more bits than required, choose the smaller number.
--
maxBitsPerRegister :: forall p n. (Finite p, KnownNat n) => Natural
maxBitsPerRegister = Haskell.min (maxBitsPerFieldElement @p) (getNatural @n)

-- | The number of bits remaining for the higher register
-- assuming that all smaller registers have the same optimal number of bits.
--
highRegisterBits :: forall p n. (Finite p, KnownNat n) => Natural
highRegisterBits = case getNatural @n `mod` maxBitsPerFieldElement @p of
                     0 -> maxBitsPerFieldElement @p
                     m -> m
-- | The lowest possible number of registers to encode @n@ bits using Field elements from @p@
-- assuming that each register storest the largest possible number of bits.
--
minNumberOfRegisters :: forall p n. (Finite p, KnownNat n) => Natural
minNumberOfRegisters = (getNatural @n + maxBitsPerRegister @p @n -! 1) `div` maxBitsPerRegister @p @n

