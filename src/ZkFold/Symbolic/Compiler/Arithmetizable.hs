{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Compiler.Arithmetizable (
        Arithmetic,
        Arithmetizable(..),
        SomeArithmetizable (..)
    ) where

import           Control.Monad.State                                 (State)
import           Data.Typeable                                       (Typeable)
import           Prelude                                             hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)
import           Type.Data.Num.Unary                                 (Natural)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                      (length, drop, take, splitAt)
import           ZkFold.Symbolic.Data.List                           (List, mapList, lengthList, indicesInteger)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit (..), Arithmetic, input)

-- | A class for arithmetizable types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the type to be arithmetized.
class Arithmetic a => Arithmetizable a x where
    -- | Arithmetizes `x`, adds it to the current circuit, and returns the outputs that make up `x`.
    arithmetize :: x -> State (ArithmeticCircuit a) [ArithmeticCircuit a]

    -- | Restores `x` from outputs from the circuits' outputs.
    restore :: [ArithmeticCircuit a] -> x

    -- | Returns the number of finite field elements needed to desscribe `x`.
    typeSize :: Integer

-- A wrapper for `Arithmetizable` types.
data SomeArithmetizable a where
    SomeArithmetizable :: (Typeable t, Arithmetizable a t) => t -> SomeArithmetizable a

instance Arithmetic a => Arithmetizable a () where
    arithmetize () = return []

    restore [] = ()
    restore _  = error "restore (): wrong number of arguments"

    typeSize = 0

instance (Arithmetizable a x, Arithmetizable a y) => Arithmetizable a (x, y) where
    arithmetize (a, b) = do
        x <- arithmetize a
        y <- arithmetize b
        return $ x ++ y

    restore rs
        | length rs /= typeSize @a @(x, y) = error "restore: wrong number of arguments"
        | otherwise = (restore rsX, restore rsY)
        where (rsX, rsY) = splitAt (typeSize @a @x) rs

    typeSize = typeSize @a @x + typeSize @a @y

instance (Arithmetizable a x, Arithmetizable a y, Arithmetizable a z) => Arithmetizable a (x, y, z) where
    arithmetize (a, b, c) = do
        x <- arithmetize a
        y <- arithmetize b
        z <- arithmetize c
        return $ x ++ y ++ z

    restore rs
        | length rs /= typeSize @a @(x, y, z) = error "restore: wrong number of arguments"
        | otherwise = (restore rsX, restore rsY, restore rsZ)
        where
            (rsX, rsYZ) = splitAt (typeSize @a @x) rs
            (rsY, rsZ)  = splitAt (typeSize @a @y) rsYZ

    typeSize = typeSize @a @x + typeSize @a @y + typeSize @a @z

instance (Arithmetizable a x, Natural n) => Arithmetizable a (List n x) where
    arithmetize xs = concat <$> mapM arithmetize xs

    restore rs
        | length rs /= typeSize @a @(List n x) = error "restore: wrong number of arguments"
        | otherwise = mapList (f rs) indicesInteger
        where
            f :: [ArithmeticCircuit a] -> Integer -> x
            f as = restore @a @x . take (typeSize @a @x) . flip drop as . ((typeSize @a @x) *)

    typeSize = typeSize @a @x * (lengthList @n)

instance (Arithmetizable a x, Arithmetizable a f) => Arithmetizable a (x -> f) where
    arithmetize f = do
        x <- mapM (const input) [1..typeSize @a @x]
        arithmetize (f $ restore x)

    restore = error "restore (x -> f): not implemented"

    typeSize = error "typeSize (x -> f): not implemented"
