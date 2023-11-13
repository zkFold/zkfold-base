{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Basic.Field (
    Zp,
    toZp,
    fromZp
    ) where

import           Data.Aeson                        (ToJSON (..), FromJSON (..))
import           Prelude                           hiding (Num(..), Fractional(..), length)
import qualified Prelude                           as Haskell

import           ZkFold.Base.Algebra.Basic.Class

newtype Zp p = Zp Integer

fromZp :: Zp p -> Integer
fromZp (Zp a) = a

toZp :: forall p . Prime p => Integer -> Zp p
toZp a = Zp $ a `mod` order @p

instance Prime p => Finite (Zp p) where
    order = order @p

instance Prime p => Prime (Zp p)

instance Prime p => Eq (Zp p) where
    Zp a == Zp b = (a - b) `mod` (order @(Zp p)) == 0

instance Prime p => Ord (Zp p) where
    Zp a <= Zp b = (a `mod` (order @(Zp p))) <= (b `mod` (order @(Zp p)))

instance Prime p => AdditiveSemigroup (Zp p) where
    Zp a + Zp b = Zp $ (a + b) `mod` (order @(Zp p))

instance Prime p => AdditiveMonoid (Zp p) where
    zero = Zp 0

instance Prime p => AdditiveGroup (Zp p) where
    negate (Zp a) = Zp $ negate a `mod` (order @(Zp p))
    Zp a - Zp b   = Zp $ (a - b) `mod` (order @(Zp p))

instance Prime p => MultiplicativeSemigroup (Zp p) where
    Zp a * Zp b = Zp $ (a * b) `mod` (order @(Zp p))

instance Prime p => MultiplicativeMonoid (Zp p) where
    one = Zp 1

instance Prime p => MultiplicativeGroup (Zp p) where
    invert (Zp a) = Zp $ snd (f (a, 1) (order @(Zp p), 0)) `mod` (order @(Zp p))
      where
        f (x, y) (x', y')
            | x' == 0   = (x, y)
            | otherwise = f (x', y') (x - q * x', y - q * y')
            where q = x `div` x'

instance Prime p => FromConstant Integer (Zp p) where
    fromConstant = toZp @p

instance Prime p => ToBits (Zp p) where
    toBits (Zp a) = map Zp $ toBits a

instance Prime p => Haskell.Num (Zp p) where
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