{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Algebra.Basic.Field (
    Zp,
    toZp,
    fromZp
    ) where

import           Prelude                           hiding (Num(..), length)

import           ZkFold.Crypto.Algebra.Basic.Class

newtype Zp p = Zp Integer
    deriving (Show)

fromZp :: Zp p -> Integer
fromZp (Zp a) = a

toZp :: forall p . Prime p => Integer -> Zp p
toZp a = Zp $ a `mod` order @p

instance Prime p => Finite (Zp p) where
    order = order @p

instance Prime p => Prime (Zp p)

instance Prime p => Eq (Zp p) where
    Zp a == Zp b = (a - b) `mod` (order @(Zp p)) == 0

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

instance Prime p => ToBits (Zp p) where
    toBits (Zp a) = map Zp $ toBits a