{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.Arithmetizable (
        Arithmetic,
        Arithmetizable (..),
        SomeArithmetizable (..),
        SomeData (..),
        SymbolicData (..),
        typeSize
    ) where

import           Data.Typeable                                       (Typeable)
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Circuit,
                                                                      concatCircuits, joinCircuits)

-- | A class for Symbolic data types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the data type.
class Arithmetic a => SymbolicData a x where

    type TypeSize a x :: Natural

    -- | Returns the circuit that makes up `x`.
    pieces :: x -> ArithmeticCircuit (TypeSize a x) a

    -- | Restores `x` from the circuit's outputs.
    restore :: Circuit a -> Vector (TypeSize a x) Natural -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall a x . KnownNat (TypeSize a x) => Natural
typeSize = value @(TypeSize a x)

-- A wrapper for `SymbolicData` types.
data SomeData a where
    SomeData :: (Typeable t, SymbolicData a t) => t -> SomeData a

instance Arithmetic a => SymbolicData a () where
    type TypeSize a () = 0

    pieces () = ArithmeticCircuit { acCircuit = mempty, acOutput = V.empty }

    restore _ _ = ()


instance
    ( SymbolicData a x
    , SymbolicData a y
    , m ~ TypeSize a x
    , KnownNat m
    ) => SymbolicData a (x, y) where

    type TypeSize a (x, y) = TypeSize a x + TypeSize a y

    pieces (a, b) = pieces a `joinCircuits` pieces b

    restore c rs = (restore c rsX, restore c rsY)
        where
            (rsX, rsY) = V.splitAt @m rs

instance
    ( SymbolicData a x
    , SymbolicData a y
    , SymbolicData a z
    , m ~ TypeSize a x
    , n ~ TypeSize a y
    , KnownNat m
    , KnownNat n
    ) => SymbolicData a (x, y, z) where

    type TypeSize a (x, y, z) = TypeSize a x + TypeSize a y + TypeSize a z

    pieces (a, b, c) = pieces a `joinCircuits` pieces b `joinCircuits` pieces c

    restore c rs = (restore c rsX, restore c rsY, restore c rsZ)
        where
            (rsX, rsY, rsZ) = V.splitAt3 @m @n rs

instance
    ( SymbolicData a x
    , m ~ TypeSize a x
    , KnownNat m
    ) => SymbolicData a (Vector n x) where

    type TypeSize a (Vector n x) = n * TypeSize a x

    pieces xs = concatCircuits $ pieces <$> xs

    restore c rs = restoreElem <$> V.chunks rs
        where
            restoreElem :: Vector m Natural -> x
            restoreElem = restore c

-- | A class for arithmetizable types, that is, a class of types whose
-- computations can be represented by arithmetic circuits.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the arithmetizable type.
class Arithmetic a => Arithmetizable a x where
    -- | The number of finite field elements needed to describe an input of `x`.
    type InputSize a x :: Natural

    -- | The number of finite field elements needed to describe the result of `x`.
    type OutputSize a x :: Natural

    -- | Given a list of circuits computing inputs, return a list of circuits
    -- computing the result of `x`.
    arithmetize :: x -> ArithmeticCircuit (InputSize a x) a -> ArithmeticCircuit (OutputSize a x) a

-- A wrapper for `Arithmetizable` types.
data SomeArithmetizable a where
    SomeArithmetizable :: (Typeable t, Arithmetizable a t) => t -> SomeArithmetizable a

-- | TODO: Overlapping instance doesn't work anymore (conflicting family instance declarations)
instance (SymbolicData a (ArithmeticCircuit n a)) => Arithmetizable a (ArithmeticCircuit n a) where
    type InputSize a (ArithmeticCircuit n a) = 0
    type OutputSize a (ArithmeticCircuit n a) = TypeSize a (ArithmeticCircuit n a)
    arithmetize x _ = pieces x

instance (Arithmetizable a f, KnownNat n, KnownNat (InputSize a f)) => Arithmetizable a (Vector n f) where
    type InputSize a (Vector n f) = n * InputSize a f
    type OutputSize a (Vector n f) = n * OutputSize a f
    arithmetize v (ArithmeticCircuit c o) = concatCircuits results
        where
            inputs  = ArithmeticCircuit c <$> V.chunks @n @(InputSize a f) o
            results = arithmetize <$> v <*> inputs

instance
    ( SymbolicData a x
    , Arithmetizable a f
    , n ~ TypeSize a x
    , KnownNat n
    ) => Arithmetizable a (x -> f) where

        type InputSize a (x -> f) = TypeSize a x + InputSize a f
        type OutputSize a (x -> f) = OutputSize a f

        arithmetize f is =
            let ArithmeticCircuit circuit outputs = is
                (xs, os) = V.splitAt @n outputs
             in arithmetize (f $ restore circuit xs) (ArithmeticCircuit circuit os)
