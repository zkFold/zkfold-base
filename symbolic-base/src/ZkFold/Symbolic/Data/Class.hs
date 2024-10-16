{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Class (
        SymbolicData (..),
    ) where

import           Control.Applicative              ((<*>))
import           Data.Function                    (flip, (.))
import           Data.Functor                     ((<$>))
import           Data.Functor.Rep                 (Representable (..))
import           Data.Kind                        (Type)
import           Data.Type.Equality               (type (~))
import           Data.Typeable                    (Proxy (..))
import           GHC.Generics                     (U1 (..), (:*:) (..), (:.:) (..))

import           ZkFold.Base.Algebra.Basic.Number (KnownNat)
import           ZkFold.Base.Control.HApplicative (HApplicative, hliftA2, hpure)
import           ZkFold.Base.Data.HFunctor        (hmap)
import           ZkFold.Base.Data.Package         (Package, pack)
import           ZkFold.Base.Data.Product         (fstP, sndP)
import           ZkFold.Base.Data.Vector          (Vector)

-- | A class for Symbolic data types.
class SymbolicData x where
    type Context x :: (Type -> Type) -> Type
    type Support x :: Type
    type Layout x :: Type -> Type

    -- | Returns the circuit that makes up `x`.
    pieces :: x -> Support x -> Context x (Layout x)

    -- | Restores `x` from the circuit's outputs.
    restore :: (Support x -> Context x (Layout x)) -> x

instance SymbolicData (c (f :: Type -> Type)) where
    type Context (c f) = c
    type Support (c f) = Proxy c
    type Layout (c f) = f

    pieces x _ = x
    restore f = f Proxy

instance HApplicative c => SymbolicData (Proxy (c :: (Type -> Type) -> Type)) where
    type Context (Proxy c) = c
    type Support (Proxy c) = Proxy c
    type Layout (Proxy c) = U1

    pieces _ _ = hpure U1
    restore _ = Proxy

instance
    ( SymbolicData x
    , SymbolicData y
    , HApplicative (Context x)
    , Context x ~ Context y
    , Support x ~ Support y
    ) => SymbolicData (x, y) where

    type Context (x, y) = Context x
    type Support (x, y) = Support x
    type Layout (x, y) = Layout x :*: Layout y

    pieces (a, b) = hliftA2 (:*:) <$> pieces a <*> pieces b
    restore f = (restore (hmap fstP . f), restore (hmap sndP . f))

instance
    ( SymbolicData x
    , SymbolicData y
    , SymbolicData z
    , HApplicative (Context x)
    , Context x ~ Context y
    , Context y ~ Context z
    , Support x ~ Support y
    , Support y ~ Support z
    ) => SymbolicData (x, y, z) where

    type Context (x, y, z) = Context (x, (y, z))
    type Support (x, y, z) = Support (x, (y, z))
    type Layout (x, y, z) = Layout (x, (y, z))

    pieces (a, b, c) = pieces (a, (b, c))
    restore f = let (a, (b, c)) = restore f in (a, b, c)

instance
    ( SymbolicData w
    , SymbolicData x
    , SymbolicData y
    , SymbolicData z
    , HApplicative (Context x)
    , Context w ~ Context x
    , Context x ~ Context y
    , Context y ~ Context z
    , Support w ~ Support x
    , Support x ~ Support y
    , Support y ~ Support z
    ) => SymbolicData (w, x, y, z) where

    type Context (w, x, y, z) = Context (w, (x, y, z))
    type Support (w, x, y, z) = Support (w, (x, y, z))
    type Layout (w, x, y, z) = Layout (w, (x, y, z))

    pieces (a, b, c, d) = pieces (a, (b, c, d))
    restore f = let (a, (b, c, d)) = restore f in (a, b, c, d)

instance
    ( SymbolicData v
    , SymbolicData w
    , SymbolicData x
    , SymbolicData y
    , SymbolicData z
    , HApplicative (Context x)
    , Context v ~ Context w
    , Context w ~ Context x
    , Context x ~ Context y
    , Context y ~ Context z
    , Support v ~ Support w
    , Support w ~ Support x
    , Support x ~ Support y
    , Support y ~ Support z
    ) => SymbolicData (v, w, x, y, z) where

    type Context (v, w, x, y, z) = Context (v, (w, x, y, z))
    type Support (v, w, x, y, z) = Support (v, (w, x, y, z))
    type Layout (v, w, x, y, z) = Layout (v, (w, x, y, z))

    pieces (a, b, c, d, e) = pieces (a, (b, c, d, e))
    restore f = let (a, (b, c, d, e)) = restore f in (a, b, c, d, e)

instance
    ( SymbolicData x
    , Package (Context x)
    , KnownNat n
    ) => SymbolicData (Vector n x) where

    type Context (Vector n x) = Context x
    type Support (Vector n x) = Support x
    type Layout (Vector n x) = Vector n :.: Layout x

    pieces xs i = pack (flip pieces i <$> xs)
    restore f = tabulate (\i -> restore (hmap (flip index i . unComp1) . f))

instance SymbolicData f => SymbolicData (x -> f) where
    type Context (x -> f) = Context f
    type Support (x -> f) = (x, Support f)
    type Layout (x -> f) = Layout f

    pieces f (x, i) = pieces (f x) i
    restore f x = restore (f . (x,))
