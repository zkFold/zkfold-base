{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.Arithmetizable (
        Arithmetic,
        Arithmetizable (..),
        SomeArithmetizable (..),
        SomeData (..),
        SymbolicData (..),
    ) where

import           Data.Typeable                                       (Typeable)
import qualified Data.Vector as V
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                             hiding (concat)
import           ZkFold.Prelude                                      (drop, length, splitAt, take)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit)

-- | A class for Symbolic data types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the data type.
class Arithmetic a => SymbolicData a x where
    -- | Returns the circuits that make up `x`.
    pieces :: x -> [ArithmeticCircuit a]

    -- | Restores `x` from the circuits' outputs.
    restore :: [ArithmeticCircuit a] -> x

    -- | Returns the number of finite field elements needed to describe `x`.
    typeSize :: Natural

-- A wrapper for `SymbolicData` types.
data SomeData a where
    SomeData :: (Typeable t, SymbolicData a t) => t -> SomeData a

instance Arithmetic a => SymbolicData a () where
    pieces () = []

    restore [] = ()
    restore _  = error "restore (): wrong number of arguments"

    typeSize = 0

instance (SymbolicData a x, SymbolicData a y) => SymbolicData a (x, y) where
    pieces (a, b) = pieces a ++ pieces b

    restore rs
        | length rs /= typeSize @a @(x, y) = error "restore: wrong number of arguments"
        | otherwise = (restore rsX, restore rsY)
        where (rsX, rsY) = splitAt (typeSize @a @x) rs

    typeSize = typeSize @a @x + typeSize @a @y

instance (SymbolicData a x, SymbolicData a y, SymbolicData a z) => SymbolicData a (x, y, z) where
    pieces (a, b, c) = pieces a ++ pieces b ++ pieces c

    restore rs
        | length rs /= typeSize @a @(x, y, z) = error "restore: wrong number of arguments"
        | otherwise = (restore rsX, restore rsY, restore rsZ)
        where
            (rsX, rsYZ) = splitAt (typeSize @a @x) rs
            (rsY, rsZ)  = splitAt (typeSize @a @y) rsYZ

    typeSize = typeSize @a @x + typeSize @a @y + typeSize @a @z

instance (SymbolicData a x, KnownNat n) => SymbolicData a (Vector n x) where
    pieces (Vector xs) = concatMap pieces xs

    restore rs
        | length rs /= typeSize @a @(Vector n x) = error "restore: wrong number of arguments"
        | otherwise = f rs <$> Vector (V.fromList [0 .. value @n -! 1])
        where
            f as = restore @a @x . take (typeSize @a @x) . flip drop as . ((typeSize @a @x) *)

    typeSize = typeSize @a @x * value @n

-- | A class for arithmetizable types, that is, a class of types whose
-- computations can be represented by arithmetic circuits.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the arithmetizable type.
class Arithmetic a => Arithmetizable a x where
    -- | Given a list of circuits computing inputs, return a list of circuits
    -- computing the result of `x`.
    arithmetize :: x -> [ArithmeticCircuit a] -> [ArithmeticCircuit a]

    -- | The number of finite field elements needed to describe an input of `x`.
    inputSize :: Natural

    -- | The number of finite field elements needed to describe the result of `x`.
    outputSize :: Natural

-- A wrapper for `Arithmetizable` types.
data SomeArithmetizable a where
    SomeArithmetizable :: (Typeable t, Arithmetizable a t) => t -> SomeArithmetizable a

instance {-# OVERLAPPABLE #-} SymbolicData a x => Arithmetizable a x where
    arithmetize x [] = pieces x
    arithmetize _ _  = error "arithmetize: wrong number of inputs"

    inputSize = 0

    outputSize = typeSize @a @x

instance (SymbolicData a x, Arithmetizable a f) => Arithmetizable a (x -> f) where
    arithmetize f is =
        let (xs, os) = splitAt (typeSize @a @x) is
         in arithmetize (f $ restore xs) os

    inputSize = typeSize @a @x + inputSize @a @f

    outputSize = outputSize @a @f
