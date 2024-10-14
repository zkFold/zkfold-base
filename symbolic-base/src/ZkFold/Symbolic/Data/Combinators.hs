{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ZkFold.Symbolic.Data.Combinators where

import           Control.Monad                    (mapM)
import           Data.Foldable                    (foldlM)
import           Data.Functor.Rep                 (Representable, mzipRep)
import           Data.Kind                        (Type)
import           Data.List                        (find, splitAt)
import           Data.List.Split                  (chunksOf)
import           Data.Maybe                       (fromMaybe)
import           Data.Proxy                       (Proxy (..))
import           Data.Ratio                       ((%))
import           Data.Traversable                 (Traversable, for)
import           Data.Type.Bool                   (If)
import           Data.Type.Ord
import           GHC.Base                         (const, return)
import           GHC.List                         (reverse)
import           GHC.TypeNats
import           Prelude                          (error, head, pure, tail, ($), (.), (<$>), (<>))
import qualified Prelude                          as Haskell
import           Type.Errors

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number (value)
import           ZkFold.Symbolic.MonadCircuit

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
    :: forall v a m
    .  MonadCircuit v a m
    => [v]
    -> Natural
    -> Natural
    -> m [v]
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
    -> (forall v m. MonadCircuit v a m => [v] -> m [v])
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
    ListRange from to = from ': ListRange (from + 1) to

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

---------------------------------------------------------------

expansion :: MonadCircuit i a m => Natural -> i -> m [i]
-- ^ @expansion n k@ computes a binary expansion of @k@ if it fits in @n@ bits.
expansion n k = do
    bits <- bitsOf n k
    k' <- horner bits
    constraint (\x -> x k - x k')
    return bits

bitsOf :: MonadCircuit i a m => Natural -> i -> m [i]
-- ^ @bitsOf n k@ creates @n@ bits and sets their witnesses equal to @n@ smaller
-- bits of @k@.
bitsOf n k = for [0 .. n -! 1] $ \j ->
    newConstrained (\x i -> let xi = x i in xi * (xi - one)) (repr j . ($ k))
    where
        repr :: WitnessField n x => Natural -> x -> x
        repr j =
              fromConstant
              . (`mod` fromConstant @Natural 2)
              . (`div` fromConstant @Natural (2 ^ j))
              . toConstant

horner :: MonadCircuit i a m => [i] -> m i
-- ^ @horner [b0,...,bn]@ computes the sum @b0 + 2 b1 + ... + 2^n bn@ using
-- Horner's scheme.
horner xs = case reverse xs of
    []       -> newAssigned (const zero)
    (b : bs) -> foldlM (\a i -> newAssigned (\x -> let xa = x a in x i + xa + xa)) b bs

splitExpansion :: (MonadCircuit i a m, Arithmetic a) => Natural -> Natural -> i -> m (i, i)
-- ^ @splitExpansion n1 n2 k@ computes two values @(l, h)@ such that
-- @k = 2^n1 h + l@, @l@ fits in @n1@ bits and @h@ fits in n2 bits (if such
-- values exist).
splitExpansion n1 n2 k = do
    l <- newRanged (fromConstant @Natural $ 2 ^ n1 -! 1) $ lower . ($ k)
    h <- newRanged (fromConstant @Natural $ 2 ^ n2 -! 1) $ upper . ($ k)
    constraint (\x -> x k - x l - scale (2 ^ n1 :: Natural) (x h))
    return (l, h)
    where
        lower :: WitnessField n a => a -> a
        lower =
            fromConstant . (`mod` fromConstant @Natural (2 ^ n1)) . toConstant

        upper :: WitnessField n a => a -> a
        upper =
            fromConstant
            . (`mod` fromConstant @Natural (2 ^ n2))
            . (`div` fromConstant @Natural (2 ^ n1))
            . toConstant

runInvert :: (MonadCircuit i a m, Representable f, Traversable f) => f i -> m (f i, f i)
runInvert is = do
    js <- for is $ \i -> newConstrained (\x j -> x i * x j) (\x -> let xi = x i in one - xi // xi)
    ks <- for (mzipRep is js) $ \(i, j) -> newConstrained (\x k -> x i * x k + x j - one) (finv . ($ i))
    return (js, ks)