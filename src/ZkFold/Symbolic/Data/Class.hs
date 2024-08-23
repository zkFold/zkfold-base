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
import           Data.Function                    (const, flip, ($), (.))
import           Data.Functor                     ((<$>))
import           Data.Kind                        (Type)
import           Data.Type.Equality               (type (~))
import           Data.Typeable                    (Proxy (..), Typeable)
import           GHC.Generics                     (Par1 (..))

import           ZkFold.Base.Algebra.Basic.Number (KnownNat, Natural, type (*), type (+), value)
import           ZkFold.Base.Control.HApplicative (HApplicative, hliftA2, hpure)
import           ZkFold.Base.Data.HFunctor        (HFunctor, hmap)
import           ZkFold.Base.Data.Package         (Package, packWith)
import qualified ZkFold.Base.Data.Vector          as V
import           ZkFold.Base.Data.Vector          (Vector)

-- | A class for Symbolic data types.
class SymbolicData x where
    type Context x :: (Type -> Type) -> Type
    type Support x :: Type
    type TypeSize x :: Natural

    -- | Returns the circuit that makes up `x`.
    pieces :: x -> Support x -> Context x (Vector (TypeSize x))

    -- | Restores `x` from the circuit's outputs.
    restore :: (Support x -> Context x (Vector (TypeSize x))) -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall x . KnownNat (TypeSize x) => Natural
typeSize = value @(TypeSize x)

-- A wrapper for `SymbolicData` types.
data SomeData c where
    SomeData :: (Typeable t, SymbolicData t, Context t ~ c) => t -> SomeData c

instance SymbolicData (c (Vector n)) where
    type Context (c (Vector n)) = c
    type Support (c (Vector n)) = Proxy c
    type TypeSize (c (Vector n)) = n

    pieces x _ = x
    restore f = f Proxy

instance HFunctor c => SymbolicData (c Par1) where
    type Context (c Par1) = c
    type Support (c Par1) = Proxy c
    type TypeSize (c Par1) = 1

    pieces = const . hmap (V.singleton . unPar1)
    restore = hmap (Par1 . V.item) . ($ Proxy)

instance HApplicative c => SymbolicData (Proxy (c :: (Type -> Type) -> Type)) where
    type Context (Proxy c) = c
    type Support (Proxy c) = Proxy c
    type TypeSize (Proxy c) = 0

    pieces _ _ = hpure V.empty
    restore _ = Proxy

instance
    ( SymbolicData x
    , SymbolicData y
    , HApplicative (Context x)
    , Context x ~ Context y
    , Support x ~ Support y
    , KnownNat (TypeSize x)
    ) => SymbolicData (x, y) where

    type Context (x, y) = Context x
    type Support (x, y) = Support x
    type TypeSize (x, y) = TypeSize x + TypeSize y

    pieces (a, b) = hliftA2 V.append <$> pieces a <*> pieces b
    restore f = (restore (hmap V.take . f), restore (hmap V.drop . f))

instance
    ( SymbolicData x
    , SymbolicData y
    , SymbolicData z
    , HApplicative (Context x)
    , Context x ~ Context y
    , Context y ~ Context z
    , Support x ~ Support y
    , Support y ~ Support z
    , KnownNat (TypeSize x)
    , KnownNat (TypeSize y)
    ) => SymbolicData (x, y, z) where

    type Context (x, y, z) = Context (x, (y, z))
    type Support (x, y, z) = Support (x, (y, z))
    type TypeSize (x, y, z) = TypeSize (x, (y, z))

    pieces (a, b, c) = pieces (a, (b, c))
    restore f = let (a, (b, c)) = restore f in (a, b, c)

instance
    ( SymbolicData x
    , Package (Context x)
    , KnownNat (TypeSize x)
    , KnownNat n
    ) => SymbolicData (Vector n x) where

    type Context (Vector n x) = Context x
    type Support (Vector n x) = Support x
    type TypeSize (Vector n x) = n * TypeSize x

    pieces xs i = packWith V.concat (flip pieces i <$> xs)
    restore f = V.generate (\i -> restore (hmap ((V.!! i) . V.chunks @n) . f))

instance SymbolicData f => SymbolicData (x -> f) where
    type Context (x -> f) = Context f
    type Support (x -> f) = (x, Support f)
    type TypeSize (x -> f) = TypeSize f

    pieces f (x, i) = pieces (f x) i
    restore f x = restore (f . (x,))
