{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.Arithmetizable (
        Arithmetic,
        SomeData (..),
        SymbolicData (..),
        typeSize
    ) where

import           Data.Kind                                           (Type)
import           Data.Typeable                                       (Typeable)
import           Prelude                                             hiding (Bool, Num (..), drop, length, product,
                                                                      splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Control.HApplicative                    (hliftA2, hpure)
import           ZkFold.Base.Data.HFunctor                           (hmap)
import           ZkFold.Base.Data.Package                            (packWith)
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit)

-- | A class for Symbolic data types.
-- Type `a` is the finite field of the arithmetic circuit.
-- Type `x` represents the data type.
class Arithmetic a => SymbolicData a x where
    type Support a x :: Type
    type TypeSize a x :: Natural

    -- | Returns the circuit that makes up `x`.
    pieces :: x -> Support a x -> ArithmeticCircuit a (Vector (TypeSize a x))

    -- | Restores `x` from the circuit's outputs.
    restore :: (Support a x -> ArithmeticCircuit a (Vector (TypeSize a x))) -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall a x . KnownNat (TypeSize a x) => Natural
typeSize = value @(TypeSize a x)

-- A wrapper for `SymbolicData` types.
data SomeData a where
    SomeData :: (Typeable t, SymbolicData a t) => t -> SomeData a

instance Arithmetic a => SymbolicData a (ArithmeticCircuit a (Vector n)) where
    type Support a (ArithmeticCircuit a (Vector n)) = ()
    type TypeSize a (ArithmeticCircuit a (Vector n)) = n

    pieces x _ = x
    restore f = f ()

instance Arithmetic a => SymbolicData a () where
    type Support a () = ()
    type TypeSize a () = 0

    pieces _ _ = hpure V.empty
    restore _ = ()

instance
    ( SymbolicData a x
    , SymbolicData a y
    , Support a x ~ Support a y
    , KnownNat (TypeSize a x)
    ) => SymbolicData a (x, y) where

    type Support a (x, y) = Support a x
    type TypeSize a (x, y) = TypeSize a x + TypeSize a y

    pieces (a, b) = hliftA2 V.append <$> pieces a <*> pieces b
    restore f = (restore (hmap V.take . f), restore (hmap V.drop . f))

instance
    ( SymbolicData a x
    , SymbolicData a y
    , SymbolicData a z
    , Support a x ~ Support a y
    , Support a y ~ Support a z
    , KnownNat (TypeSize a x)
    , KnownNat (TypeSize a y)
    ) => SymbolicData a (x, y, z) where

    type Support a (x, y, z) = Support a (x, (y, z))
    type TypeSize a (x, y, z) = TypeSize a (x, (y, z))

    pieces (a, b, c) = pieces (a, (b, c))
    restore f = let (a, (b, c)) = restore f in (a, b, c)

instance
    ( SymbolicData a x
    , KnownNat (TypeSize a x)
    , KnownNat n
    ) => SymbolicData a (Vector n x) where

    type Support a (Vector n x) = Support a x
    type TypeSize a (Vector n x) = n * TypeSize a x

    pieces xs i = packWith V.concat (flip pieces i <$> xs)
    restore f = V.generate (\i -> restore (hmap ((V.!! i) . V.chunks @n) . f))

instance SymbolicData a f => SymbolicData a (x -> f) where
    type Support a (x -> f) = (x, Support a f)
    type TypeSize a (x -> f) = TypeSize a f

    pieces f (x, i) = pieces (f x) i
    restore f x = restore (f . (x,))
