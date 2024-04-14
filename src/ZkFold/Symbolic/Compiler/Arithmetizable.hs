{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Compiler.Arithmetizable (
        Arithmetic,
        Arithmetizable(..),
        MonadBlueprint(..),
        SomeArithmetizable (..),
        circuit,
        circuits,
    ) where

import           Data.Typeable                                             (Typeable)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Num (..), drop, length, product,
                                                                            splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                                   hiding (concat)
import           ZkFold.Prelude                                            (drop, length, replicateA, splitAt, take)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Arithmetic, ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit, circuits)

-- | A class for arithmetizable types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the type to be arithmetized.
class Arithmetic a => Arithmetizable a x where
    -- | Arithmetizes `x`, adds it to the current circuit, and returns the outputs that make up `x`.
    arithmetize :: MonadBlueprint i a m => x -> m [i]

    -- | Restores `x` from outputs from the circuits' outputs.
    restore :: [ArithmeticCircuit a] -> x

    -- | Returns the number of finite field elements needed to describe `x`.
    typeSize :: Natural

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

instance (Arithmetizable a x, KnownNat n) => Arithmetizable a (Vector n x) where
    arithmetize (Vector xs) = concat <$> mapM arithmetize xs

    restore rs
        | length rs /= typeSize @a @(Vector n x) = error "restore: wrong number of arguments"
        | otherwise = f rs <$> Vector [0 .. value @n -! 1]
        where
            f as = restore @a @x . take (typeSize @a @x) . flip drop as . ((typeSize @a @x) *)

    typeSize = typeSize @a @x * value @n

instance (Arithmetizable a x, Arithmetizable a f) => Arithmetizable a (x -> f) where
    arithmetize f = do
        x <- replicateA (typeSize @a @x) (input >>= output)
        arithmetize (f $ restore x)

    restore = error "restore (x -> f): not implemented"

    typeSize = error "typeSize (x -> f): not implemented"
