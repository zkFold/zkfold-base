{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.Field (
    IrreduciblePoly(..),
    Zp,
    toZp,
    fromZp,
    Ext2(..),
    Ext3(..)
    ) where

import           Control.DeepSeq                            (NFData (..))
import           Data.Aeson                                 (FromJSON (..), ToJSON (..))
import           Data.Bifunctor                             (first)
import           Data.Bool                                  (bool)
import qualified Data.Vector                                as V
import           GHC.Generics                               (Generic)
import           Numeric.Natural                            (Natural)
import           Prelude                                    hiding (Fractional (..), Num (..), length, (^))
import qualified Prelude                                    as Haskell
import           System.Random                              (Random (..), RandomGen, mkStdGen, uniformR)
import           Test.QuickCheck                            hiding (scale)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString

------------------------------ Prime Fields -----------------------------------

newtype Zp (p :: Natural) = Zp Integer
    deriving (Generic, NFData)

fromZp :: Zp p -> Natural
fromZp (Zp a) = fromIntegral a

residue :: forall p . KnownNat p => Integer -> Integer
residue = (`mod` fromIntegral (value @p))

toZp :: forall p . KnownNat p => Integer -> Zp p
toZp = Zp . residue @p

instance KnownNat p => Finite (Zp p) where
    type Order (Zp p) = p

instance KnownNat p => Eq (Zp p) where
    Zp a == Zp b = residue @p (a - b) == 0

instance KnownNat p => Ord (Zp p) where
    Zp a <= Zp b = residue @p a <= residue @p b

instance KnownNat p => AdditiveSemigroup (Zp p) where
    Zp a + Zp b = toZp (a + b)

instance KnownNat p => Scale Natural (Zp p) where
    scale c (Zp a) = toZp (scale c a)

instance KnownNat p => AdditiveMonoid (Zp p) where
    zero = Zp 0

instance KnownNat p => Scale Integer (Zp p) where
    scale c (Zp a) = toZp (scale c a)

instance KnownNat p => AdditiveGroup (Zp p) where
    negate (Zp a) = toZp (negate a)
    Zp a - Zp b   = toZp (a - b)

instance KnownNat p => MultiplicativeSemigroup (Zp p) where
    Zp a * Zp b = toZp (a * b)

instance KnownNat p => Exponent Natural (Zp p) where
    (^) = natPow

instance KnownNat p => MultiplicativeMonoid (Zp p) where
    one = Zp 1

instance KnownNat p => FromConstant Natural (Zp p) where
    fromConstant = toZp . fromConstant

instance KnownNat p => Semiring (Zp p)

instance KnownNat p => FromConstant Integer (Zp p) where
    fromConstant = toZp

instance KnownNat p => Ring (Zp p)

instance Prime p => Exponent Integer (Zp p) where
    -- | By Fermat's little theorem
    a ^ n = intPowF a (n `mod` (fromConstant (value @p) - 1))

instance Prime p => Field (Zp p) where
    finv (Zp a) = toZp $ snd (f (a, 1) (p, 0))
      where
        p = fromIntegral (order @(Zp p))
        f (x, y) (x', y')
            | x' == 0   = (x, y)
            | otherwise = f (x', y') (x - q * x', y - q * y')
            where q = x `div` x'

    rootOfUnity l
      | l == 0                       = Nothing
      | (value @p -! 1) `mod` n /= 0 = Nothing
      | otherwise = Just $ rootOfUnity' (mkStdGen 0)
        where
          n = 2 ^ l
          rootOfUnity' :: RandomGen g => g -> Zp p
          rootOfUnity' g =
              let (x, g') = first fromConstant $ uniformR (1, value @p -! 1) g
                  x' = x ^ ((value @p -! 1) `div` n)
              in bool (rootOfUnity' g') x' (x' ^ (n `div` 2) /= one)

instance Prime p => BinaryExpansion (Zp p) where
    binaryExpansion = map (Zp . fromConstant) . binaryExpansion . fromZp

instance KnownNat p => Haskell.Num (Zp p) where
    fromInteger = toZp
    (+)         = (+)
    (-)         = (-)
    (*)         = (*)
    negate      = negate
    abs         = id
    signum      = const 1

instance Prime p => Haskell.Fractional (Zp p) where
    fromRational = error "`fromRational` is not implemented for `Zp p`"
    recip        = finv
    (/)          = (//)

instance Show (Zp p) where
    show (Zp a) = show a

instance ToJSON (Zp p) where
    toJSON (Zp a) = toJSON a

instance FromJSON (Zp p) where
    parseJSON = fmap Zp . parseJSON

instance ToByteString (Zp p) where
    toByteString (Zp a) = toByteString a

instance FromByteString (Zp p) where
    fromByteString = fmap Zp . fromByteString

instance KnownNat p => Arbitrary (Zp p) where
    arbitrary = toZp <$> chooseInteger (0, fromIntegral (order @(Zp p)) - 1)

instance KnownNat p => Random (Zp p) where
    randomR (Zp a, Zp b) g = (Zp r, g')
      where
        (r, g') = randomR (a, b) g

    random g = (Zp r, g')
      where
        (r, g') = randomR (0, fromIntegral (order @(Zp p)) - 1) g

-- | Exponentiation by an element of a finite field is well-defined (and lawful)
-- if and only if the base is a finite multiplicative group of a matching order.
--
-- Note that left distributivity is satisfied, meaning
-- @a ^ (m + n) = (a ^ m) * (a ^ n)@.
instance (KnownNat p, MultiplicativeGroup a, Order a ~ p) => Exponent (Zp p) a where
    a ^ n = a ^ fromZp n

----------------------------- Field Extensions --------------------------------

class IrreduciblePoly f e | e -> f where
    irreduciblePoly :: Poly f

data Ext2 f e = Ext2 f f
    deriving (Eq, Show)

instance KnownNat (Order (Ext2 f e)) => Finite (Ext2 f e) where
    type Order (Ext2 f e) = Order f ^ 2

instance Field f => AdditiveSemigroup (Ext2 f e) where
    Ext2 a b + Ext2 c d = Ext2 (a + c) (b + d)

instance Scale c f => Scale c (Ext2 f e) where
    scale c (Ext2 a b) = Ext2 (scale c a) (scale c b)

instance Field f => AdditiveMonoid (Ext2 f e) where
    zero = Ext2 zero zero

instance Field f => AdditiveGroup (Ext2 f e) where
    negate (Ext2 a b) = Ext2 (negate a) (negate b)
    Ext2 a b - Ext2 c d = Ext2 (a - c) (b - d)

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeSemigroup (Ext2 f e) where
    Ext2 a b * Ext2 c d = case snd $ qr (toPoly [a, b] * toPoly [c, d]) (irreduciblePoly @f @e) of
            P []  -> Ext2 zero zero
            P [x] -> Ext2 x zero
            P v   -> Ext2 (v V.! 0) (v V.! 1)

instance MultiplicativeMonoid (Ext2 f e) => Exponent Natural (Ext2 f e) where
    (^) = natPow

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeMonoid (Ext2 f e) where
    one = Ext2 one zero

instance Field (Ext2 f e) => Exponent Integer (Ext2 f e) where
    (^) = intPowF

instance (Field f, Eq f, IrreduciblePoly f e) => Field (Ext2 f e) where
    finv (Ext2 a b) =
        let (g, s) = eea (toPoly [a, b]) (irreduciblePoly @f @e)
        in case scaleP (one // lt g) 0 s of
            P []  -> Ext2 zero zero
            P [x] -> Ext2 x zero
            P v   -> Ext2 (v V.! 0) (v V.! 1)

    rootOfUnity n = (\r -> Ext2 r zero) <$> rootOfUnity n

instance (FromConstant f f', Field f') => FromConstant f (Ext2 f' e) where
    fromConstant e = Ext2 (fromConstant e) zero

instance (Field f, Eq f, IrreduciblePoly f e) => Semiring (Ext2 f e)

instance (Field f, Eq f, IrreduciblePoly f e) => Ring (Ext2 f e)

instance ToByteString f => ToByteString (Ext2 f e) where
    toByteString (Ext2 a b) = toByteString a <> toByteString b

instance (Field f, Eq f, IrreduciblePoly f e, Arbitrary f) => Arbitrary (Ext2 f e) where
    arbitrary = Ext2 <$> arbitrary <*> arbitrary

data Ext3 f e = Ext3 f f f
    deriving (Eq, Show)

instance KnownNat (Order (Ext3 f e)) => Finite (Ext3 f e) where
    type Order (Ext3 f e) = Order f ^ 3

instance Field f => AdditiveSemigroup (Ext3 f e) where
    Ext3 a b c + Ext3 d e f = Ext3 (a + d) (b + e) (c + f)

instance Scale c f => Scale c (Ext3 f e) where
    scale c' (Ext3 a b c) = Ext3 (scale c' a) (scale c' b) (scale c' c)

instance Field f => AdditiveMonoid (Ext3 f e) where
    zero = Ext3 zero zero zero

instance Field f => AdditiveGroup (Ext3 f e) where
    negate (Ext3 a b c) = Ext3 (negate a) (negate b) (negate c)
    Ext3 a b c - Ext3 d e f = Ext3 (a - d) (b - e) (c - f)

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeSemigroup (Ext3 f e) where
    Ext3 a b c * Ext3 d e f = case snd $ qr (toPoly [a, b, c] * toPoly [d, e, f]) (irreduciblePoly @f @e) of
            P []     -> Ext3 zero zero zero
            P [x]    -> Ext3 x zero zero
            P [x, y] -> Ext3 x y zero
            P v      -> Ext3 (v V.! 0) (v V.! 1) (v V.! 2)

instance MultiplicativeMonoid (Ext3 f e) => Exponent Natural (Ext3 f e) where
    (^) = natPow

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeMonoid (Ext3 f e) where
    one = Ext3 one zero zero

instance Field (Ext3 f e) => Exponent Integer (Ext3 f e) where
    (^) = intPowF

instance (Field f, Eq f, IrreduciblePoly f e) => Field (Ext3 f e) where
    finv (Ext3 a b c) =
        let (g, s) = eea (toPoly [a, b, c]) (irreduciblePoly @f @e)
        in case scaleP (one // lt g) 0 s of
            P []     -> Ext3 zero zero zero
            P [x]    -> Ext3 x zero zero
            P [x, y] -> Ext3 x y zero
            P v      -> Ext3 (v V.! 0) (v V.! 1) (v V.! 2)

    rootOfUnity n = (\r -> Ext3 r zero zero) <$> rootOfUnity n

instance (FromConstant f f', Field f') => FromConstant f (Ext3 f' ip) where
    fromConstant e = Ext3 (fromConstant e) zero zero

instance (Field f, Eq f, IrreduciblePoly f e) => Semiring (Ext3 f e)

instance (Field f, Eq f, IrreduciblePoly f e) => Ring (Ext3 f e)

instance ToByteString f => ToByteString (Ext3 f e) where
    toByteString (Ext3 a b c) = toByteString a <> toByteString b <> toByteString c

instance (Field f, Eq f, IrreduciblePoly f e, Arbitrary f) => Arbitrary (Ext3 f e) where
    arbitrary = Ext3 <$> arbitrary <*> arbitrary <*> arbitrary
