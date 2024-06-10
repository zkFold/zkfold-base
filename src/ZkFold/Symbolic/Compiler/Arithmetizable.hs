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
class (Arithmetic a, KnownNat n) => SymbolicData a n x | x a -> n where
    -- | Returns the circuit that makes up `x`.
    pieces :: x -> ArithmeticCircuit n a

    -- | Restores `x` from the circuit's outputs.
    restore :: Circuit a -> Vector n Natural -> x

    -- | Returns the number of finite field elements needed to describe `x`.
    typeSize :: Natural
    typeSize = value @n

-- A wrapper for `SymbolicData` types.
data SomeData a where
    SomeData :: (Typeable t, SymbolicData a n t) => t -> SomeData a

instance Arithmetic a => SymbolicData a 0 () where
    pieces () = ArithmeticCircuit { acCircuit = mempty, acOutput = V.empty }

    restore _ _ = ()

instance (SymbolicData a m x, SymbolicData a n y, s ~ m + n, s - m ~ n, KnownNat s) => SymbolicData a s (x, y) where
    pieces (a, b) = pieces a `joinCircuits` pieces b

    restore c rs = (restore c rsX, restore c rsY)
        where
            (rsX, rsY) = (V.take @m rs, V.drop @m rs)

instance
    ( SymbolicData a m x
    , SymbolicData a n y
    , SymbolicData a k z
    , s ~ m + n + k
    , ((s - m) - n) ~ k
    , KnownNat s
    ) => SymbolicData a s (x, y, z) where
    pieces (a, b, c) = pieces a `joinCircuits` pieces b `joinCircuits` pieces c

    restore c rs = (restore c rsX, restore c rsY, restore c rsZ)
        where
            (rsX, rsYZ) = (V.take @m rs, V.drop @m rs)
            (rsY, rsZ)  = (V.take @n rsYZ, V.drop @n rsYZ)

instance (SymbolicData a m x, KnownNat n, s ~ n * m, KnownNat s) => SymbolicData a s (Vector n x) where
    pieces xs = concatCircuits $ pieces <$> xs

    restore c rs = restoreElem <$> V.chunks rs
        where
            restoreElem :: Vector m Natural -> x
            restoreElem = restore c

-- | A class for arithmetizable types, that is, a class of types whose
-- computations can be represented by arithmetic circuits.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the arithmetizable type.
class (Arithmetic a, KnownNat i, KnownNat o) => Arithmetizable a i o x where
    -- | Given a list of circuits computing inputs, return a list of circuits
    -- computing the result of `x`.
    arithmetize :: x -> ArithmeticCircuit i a -> ArithmeticCircuit o a

    -- | The number of finite field elements needed to describe an input of `x`.
    inputSize :: Natural
    inputSize = value @i

    -- | The number of finite field elements needed to describe the result of `x`.
    outputSize :: Natural
    outputSize = value @o

-- A wrapper for `Arithmetizable` types.
data SomeArithmetizable a where
    SomeArithmetizable :: (Typeable t, Arithmetizable a i o t) => t -> SomeArithmetizable a

instance {-# OVERLAPPABLE #-} SymbolicData a n x => Arithmetizable a 0 n x where
    arithmetize x _ = pieces x

instance
    ( SymbolicData a n x
    , Arithmetizable a i o f
    , s ~ i + n
    , i ~ s - n
    , KnownNat s
    , KnownNat o
    ) => Arithmetizable a s o (x -> f) where
    arithmetize f is =
        let ArithmeticCircuit circuit outputs = is
            (xs, os) = (V.take @n outputs, V.drop @n outputs)
         in arithmetize (f $ restore circuit xs) (ArithmeticCircuit circuit os)
