{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Basic.Field (
    IrreduciblePoly(..),
    Zp,
    toZp,
    fromZp,
    Ext2(..),
    Ext3(..)
    ) where

import           Data.Aeson                        (ToJSON (..), FromJSON (..))
import           Prelude                           hiding (Num(..), Fractional(..), length, (^))
import qualified Prelude                           as Haskell
import           Test.QuickCheck                   hiding (scale)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString

------------------------------ Prime Fields -----------------------------------

newtype Zp p = Zp Integer

fromZp :: Zp p -> Integer
fromZp (Zp a) = a

toZp :: forall p . Finite p => Integer -> Zp p
toZp a = Zp $ a `mod` order @p

instance Finite p => Finite (Zp p) where
    order = order @p

instance Prime p => Prime (Zp p)

instance Finite p => Eq (Zp p) where
    Zp a == Zp b = (a - b) `mod` (order @(Zp p)) == 0

instance Finite p => Ord (Zp p) where
    Zp a <= Zp b = (a `mod` (order @(Zp p))) <= (b `mod` (order @(Zp p)))

instance Finite p => AdditiveSemigroup (Zp p) where
    Zp a + Zp b = Zp $ (a + b) `mod` (order @(Zp p))

instance Finite p => AdditiveMonoid (Zp p) where
    zero = Zp 0

instance Finite p => AdditiveGroup (Zp p) where
    negate (Zp a) = Zp $ negate a `mod` (order @(Zp p))
    Zp a - Zp b   = Zp $ (a - b) `mod` (order @(Zp p))

instance Finite p => MultiplicativeSemigroup (Zp p) where
    Zp a * Zp b = Zp $ (a * b) `mod` (order @(Zp p))

instance Finite p => MultiplicativeMonoid (Zp p) where
    one = Zp 1

instance Prime p => MultiplicativeGroup (Zp p) where
    invert (Zp a) = Zp $ snd (f (a, 1) (order @(Zp p), 0)) `mod` (order @(Zp p))
      where
        f (x, y) (x', y')
            | x' == 0   = (x, y)
            | otherwise = f (x', y') (x - q * x', y - q * y')
            where q = x `div` x'

instance Finite p => FromConstant Integer (Zp p) where
    fromConstant = toZp @p

instance Finite p => ToBits (Zp p) where
    toBits (Zp a) = map Zp $ toBits a

instance Finite p => FromBits (Zp p) where
    fromBits = toZp . fromBits . map fromZp

instance (AdditiveMonoid a, Finite p) => Scale a (Zp p) where
    scale (Zp n) = scale n

instance (MultiplicativeMonoid a, Finite p) => Exponent a (Zp p) where
    a ^ Zp n = a ^ n

instance Finite p => Haskell.Num (Zp p) where
    fromInteger = toZp @p
    (+)         = (+)
    (-)         = (-)
    (*)         = (*)
    negate      = negate
    abs         = id
    signum      = const 1

instance Prime p => Haskell.Fractional (Zp p) where
    fromRational = error "`fromRational` is not implemented for `Zp p`"
    recip        = invert
    (/)          = (/)

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

instance Finite p => Arbitrary (Zp p) where
    arbitrary = toZp <$> chooseInteger (0, order @(Zp p) - 1)

----------------------------- Field Extensions --------------------------------

class IrreduciblePoly f e | e -> f where
    irreduciblePoly :: Poly f

data Ext2 f e = Ext2 f f
    deriving (Eq, Show)

instance Finite f => Finite (Ext2 f e) where
    order = order @f * order @f

instance Field f => AdditiveSemigroup (Ext2 f e) where
    Ext2 a b + Ext2 c d = Ext2 (a + c) (b + d)

instance Field f => AdditiveMonoid (Ext2 f e) where
    zero = Ext2 zero zero

instance Field f => AdditiveGroup (Ext2 f e) where
    negate (Ext2 a b) = Ext2 (negate a) (negate b)
    Ext2 a b - Ext2 c d = Ext2 (a - c) (b - d)

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeSemigroup (Ext2 f e) where
    Ext2 a b * Ext2 c d = case snd $ qr (toPoly [a, b] * toPoly [c, d]) (irreduciblePoly @f @e) of
            P (x:y:_) -> Ext2 x y
            P [x]     -> Ext2 x zero
            P []      -> Ext2 zero zero

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeMonoid (Ext2 f e) where
    one = Ext2 one zero

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeGroup (Ext2 f e) where
    invert (Ext2 a b) =
        let (g, s) = eea (toPoly [a, b]) (irreduciblePoly @f @e)
        in case scaleP (one / lt g) 0 s of
            P (x:y:_) -> Ext2 x y
            P [x]     -> Ext2 x zero
            P []      -> Ext2 zero zero

instance (FromConstant f f', Field f') => FromConstant f (Ext2 f' e) where
    fromConstant e = Ext2 (fromConstant e) zero

instance (Field f, ToBits f, Eq f, IrreduciblePoly f e) => ToBits (Ext2 f e) where
    toBits (Ext2 a b) = map (`Ext2` zero) $ toBits a ++ toBits b

instance ToByteString f => ToByteString (Ext2 f e) where
    toByteString (Ext2 a b) = toByteString a <> toByteString b

instance (Field f, Eq f, IrreduciblePoly f e, Arbitrary f) => Arbitrary (Ext2 f e) where
    arbitrary = Ext2 <$> arbitrary <*> arbitrary

data Ext3 f e = Ext3 f f f
    deriving (Eq, Show)

instance Finite f => Finite (Ext3 f e) where
    order = order @f * order @f * order @f

instance Field f => AdditiveSemigroup (Ext3 f e) where
    Ext3 a b c + Ext3 d e f = Ext3 (a + d) (b + e) (c + f)

instance Field f => AdditiveMonoid (Ext3 f e) where
    zero = Ext3 zero zero zero

instance Field f => AdditiveGroup (Ext3 f e) where
    negate (Ext3 a b c) = Ext3 (negate a) (negate b) (negate c)
    Ext3 a b c - Ext3 d e f = Ext3 (a - d) (b - e) (c - f)

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeSemigroup (Ext3 f e) where
    Ext3 a b c * Ext3 d e f = case snd $ qr (toPoly [a, b, c] * toPoly [d, e, f]) (irreduciblePoly @f @e) of
            P (x:y:z:_) -> Ext3 x y z
            P [x, y]    -> Ext3 x y zero
            P [x]       -> Ext3 x zero zero
            P []        -> Ext3 zero zero zero

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeMonoid (Ext3 f e) where
    one = Ext3 one zero zero

instance (Field f, Eq f, IrreduciblePoly f e) => MultiplicativeGroup (Ext3 f e) where
    invert (Ext3 a b c) =
        let (g, s) = eea (toPoly [a, b, c]) (irreduciblePoly @f @e)
        in case scaleP (one / lt g) 0 s of
            P (x:y:z:_) -> Ext3 x y z
            P [x, y]    -> Ext3 x y zero
            P [x]       -> Ext3 x zero zero
            P []        -> Ext3 zero zero zero

instance (FromConstant f f', Field f') => FromConstant f (Ext3 f' ip) where
    fromConstant e = Ext3 (fromConstant e) zero zero

instance (Field f, ToBits f, Eq f, IrreduciblePoly f e) => ToBits (Ext3 f e) where
    toBits (Ext3 a b c) = map (\x -> Ext3 x zero zero) $ toBits a ++ toBits b ++ toBits c

instance ToByteString f => ToByteString (Ext3 f e) where
    toByteString (Ext3 a b c) = toByteString a <> toByteString b <> toByteString c

instance (Field f, Eq f, IrreduciblePoly f e, Arbitrary f) => Arbitrary (Ext3 f e) where
    arbitrary = Ext3 <$> arbitrary <*> arbitrary <*> arbitrary
