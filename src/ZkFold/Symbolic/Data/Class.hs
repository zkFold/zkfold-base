{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Class (
        SomeData (..),
        SymbolicData (..),
        typeSize
    ) where

import           Control.Applicative              ((<*>))
import           Data.Function                    (flip, (.))
import           Data.Functor                     ((<$>))
import           Data.Kind                        (Type)
import           Data.Type.Equality               (type (~))
import           Data.Typeable                    (Typeable)

import           ZkFold.Base.Algebra.Basic.Number (KnownNat, Natural, type (*), type (+), value)
import           ZkFold.Base.Control.HApplicative (HApplicative, hliftA2, hpure)
import           ZkFold.Base.Data.HFunctor        (hmap)
import           ZkFold.Base.Data.Package         (Package, packWith)
import qualified ZkFold.Base.Data.Vector          as V
import           ZkFold.Base.Data.Vector          (Vector)

-- | A class for Symbolic data types.
-- Type `c` is the type of computational context.
-- Type `x` represents the data type.
class SymbolicData c x where
    type Support c x :: Type
    type TypeSize c x :: Natural

    -- | Returns the circuit that makes up `x`.
    pieces :: x -> Support c x -> c (Vector (TypeSize c x))

    -- | Restores `x` from the circuit's outputs.
    restore :: (Support c x -> c (Vector (TypeSize c x))) -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall c x . KnownNat (TypeSize c x) => Natural
typeSize = value @(TypeSize c x)

-- A wrapper for `SymbolicData` types.
data SomeData c where
    SomeData :: (Typeable t, SymbolicData c t) => t -> SomeData c

instance SymbolicData c (c (Vector n)) where
    type Support c (c (Vector n)) = ()
    type TypeSize c (c (Vector n)) = n

    pieces x _ = x
    restore f = f ()

instance HApplicative c => SymbolicData c () where
    type Support c () = ()
    type TypeSize c () = 0

    pieces _ _ = hpure V.empty
    restore _ = ()

instance
    ( HApplicative c
    , SymbolicData c x
    , SymbolicData c y
    , Support c x ~ Support c y
    , KnownNat (TypeSize c x)
    ) => SymbolicData c (x, y) where

    type Support c (x, y) = Support c x
    type TypeSize c (x, y) = TypeSize c x + TypeSize c y

    pieces (a, b) = hliftA2 V.append <$> pieces a <*> pieces b
    restore f = (restore (hmap V.take . f), restore (hmap V.drop . f))

instance
    ( HApplicative c
    , SymbolicData c x
    , SymbolicData c y
    , SymbolicData c z
    , Support c x ~ Support c y
    , Support c y ~ Support c z
    , KnownNat (TypeSize c x)
    , KnownNat (TypeSize c y)
    ) => SymbolicData c (x, y, z) where

    type Support c (x, y, z) = Support c (x, (y, z))
    type TypeSize c (x, y, z) = TypeSize c (x, (y, z))

    pieces (a, b, c) = pieces (a, (b, c))
    restore f = let (a, (b, c)) = restore f in (a, b, c)

instance
    ( Package c
    , SymbolicData c x
    , KnownNat (TypeSize c x)
    , KnownNat n
    ) => SymbolicData c (Vector n x) where

    type Support c (Vector n x) = Support c x
    type TypeSize c (Vector n x) = n * TypeSize c x

    pieces xs i = packWith V.concat (flip pieces i <$> xs)
    restore f = V.generate (\i -> restore (hmap ((V.!! i) . V.chunks @n) . f))

instance SymbolicData c f => SymbolicData c (x -> f) where
    type Support c (x -> f) = (x, Support c f)
    type TypeSize c (x -> f) = TypeSize c f

    pieces f (x, i) = pieces (f x) i
    restore f x = restore (f . (x,))
