{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
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
import           Prelude                                             hiding (Bool, Num (..), drop, length, product,
                                                                      splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Control.HApplicative                    (hliftA2)
import           ZkFold.Base.Data.Package                            (packWith)
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Circuit)

-- | A class for Symbolic data types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the data type.
class Arithmetic a => SymbolicData a x where

    type TypeSize a x :: Natural

    -- | Returns the circuit that makes up `x`.
    pieces :: x -> ArithmeticCircuit a (Vector (TypeSize a x))

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

    pieces (a, b) = hliftA2 V.append (pieces a) (pieces b)

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

    pieces (a, b, c) = hliftA2 V.append (hliftA2 V.append (pieces a) (pieces b)) (pieces c)

    restore c rs = (restore c rsX, restore c rsY, restore c rsZ)
        where
            (rsX, rsY, rsZ) = V.splitAt3 @m @n rs

instance
    ( SymbolicData a x
    , m ~ TypeSize a x
    , KnownNat m
    ) => SymbolicData a (Vector n x) where

    type TypeSize a (Vector n x) = n * TypeSize a x

    pieces xs = packWith V.concat (pieces <$> xs)

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
    arithmetize :: x -> ArithmeticCircuit a (Vector (InputSize a x)) -> ArithmeticCircuit a (Vector (OutputSize a x))

-- A wrapper for `Arithmetizable` types.
data SomeArithmetizable a where
    SomeArithmetizable :: (Typeable t, Arithmetizable a t) => t -> SomeArithmetizable a

-- | TODO: Overlapping instance doesn't work anymore (conflicting family instance declarations)
instance (SymbolicData a (ArithmeticCircuit a n)) => Arithmetizable a (ArithmeticCircuit a n) where
    type InputSize a (ArithmeticCircuit a n) = 0
    type OutputSize a (ArithmeticCircuit a n) = TypeSize a (ArithmeticCircuit a n)
    arithmetize x _ = pieces x

instance (Arithmetizable a f, KnownNat n, KnownNat (InputSize a f)) => Arithmetizable a (Vector n f) where
    type InputSize a (Vector n f) = n * InputSize a f
    type OutputSize a (Vector n f) = n * OutputSize a f
    arithmetize v (ArithmeticCircuit c o) = packWith V.concat results
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
