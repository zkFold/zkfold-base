{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ZkFold.Symbolic.Data.Combinators where

import           Control.Monad                                             (mapM)
import           Data.List                                                 (find, splitAt)
import           Data.List.Split                                           (chunksOf)
import           Data.Maybe                                                (fromMaybe)
import           Data.Proxy                                                (Proxy (..))
import           Data.Ratio                                                ((%))
import           GHC.TypeNats                                              (KnownNat, Natural, natVal)
import           Prelude                                                   (div, error, mod, pure, ($), (.), (<$>),
                                                                            (<>))
import qualified Prelude                                                   as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
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
    :: forall a
    .  ArithmeticCircuit a
    -> [ArithmeticCircuit a]
    -> Natural
    -> Natural
    -> (forall i m. MonadBlueprint i a m => m [i])
toBits hi lo hiBits loBits = do
    lows <- mapM runCircuit lo
    high <- runCircuit hi

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


maxOverflow :: forall a n . (Finite a, KnownNat n) => Natural
maxOverflow = registerSize @a @n + Haskell.ceiling (log2 $ numberOfRegisters @a @n)

highRegisterSize :: forall a n . (Finite a, KnownNat n) => Natural
highRegisterSize = getNatural @n -! registerSize @a @n * (numberOfRegisters @a @n -! 1)

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
             in Haskell.floor $ (bitLimit -! maxAdded) % 2

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

