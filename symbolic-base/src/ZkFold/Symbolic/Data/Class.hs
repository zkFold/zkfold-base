{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Class (
        SymbolicData (..),
        GSymbolicData (..)
    ) where

import           Control.Applicative              ((<*>))
import           Data.Bifunctor                   (bimap)
import           Data.Function                    (flip, (.))
import           Data.Functor                     ((<$>))
import           Data.Functor.Rep                 (Representable (..))
import           Data.Kind                        (Type)
import           Data.Traversable                 (Traversable)
import           Data.Tuple                       (fst)
import           Data.Type.Equality               (type (~))
import           Data.Typeable                    (Proxy (..))
import           GHC.Generics                     (U1 (..), (:*:) (..), (:.:) (..))
import qualified GHC.Generics                     as G

import           ZkFold.Base.Algebra.Basic.Number (KnownNat)
import           ZkFold.Base.Control.HApplicative (HApplicative, hliftA2, hpure)
import           ZkFold.Base.Data.HFunctor        (hmap)
import           ZkFold.Base.Data.Package         (Package, pack)
import           ZkFold.Base.Data.Product         (fstP, sndP)
import           ZkFold.Base.Data.Vector          (Vector)
import           ZkFold.Symbolic.Class            (Symbolic (WitnessField))

-- | A class for Symbolic data types.
class
    ( Representable (Layout x)
    , Traversable (Layout x)
    ) => SymbolicData x where

    type Context x :: (Type -> Type) -> Type
    type Context x = GContext (G.Rep x)

    type Support x :: Type
    type Support x = GSupport (G.Rep x)

    type Layout x :: Type -> Type
    type Layout x = GLayout (G.Rep x)

    type Payload x :: Type -> Type
    type Payload x = GPayload (G.Rep x)

    -- | Returns the circuit that makes up `x`.
    arithmetize :: x -> Support x -> Context x (Layout x)
    default arithmetize
      :: ( G.Generic x
         , GSymbolicData (G.Rep x)
         , Context x ~ GContext (G.Rep x)
         , Support x ~ GSupport (G.Rep x)
         , Layout x ~ GLayout (G.Rep x)
         )
      => x -> Support x -> Context x (Layout x)
    arithmetize x = garithmetize (G.from x)

    payload :: x -> Support x -> Payload x (WitnessField (Context x))
    default payload
      :: ( G.Generic x
         , GSymbolicData (G.Rep x)
         , Context x ~ GContext (G.Rep x)
         , Support x ~ GSupport (G.Rep x)
         , Payload x ~ GPayload (G.Rep x)
         )
      => x -> Support x -> Payload x (WitnessField (Context x))
    payload x = gpayload (G.from x)

    -- | Restores `x` from the circuit's outputs.
    restore ::
      Context x ~ c =>
      (Support x -> (c (Layout x), Payload x (WitnessField c))) -> x
    default restore ::
      ( Context x ~ c, G.Generic x, GSymbolicData (G.Rep x)
      , Context x ~ GContext (G.Rep x)
      , Support x ~ GSupport (G.Rep x)
      , Layout x ~ GLayout (G.Rep x)
      , Payload x ~ GPayload (G.Rep x)) =>
      (Support x -> (c (Layout x), Payload x (WitnessField c))) -> x
    restore f = G.to (grestore f)

instance
    ( Representable f
    , Traversable f
    ) => SymbolicData (c (f :: Type -> Type)) where

    type Context (c f) = c
    type Support (c f) = Proxy c
    type Layout (c f) = f
    type Payload (c f) = U1

    arithmetize x _ = x
    payload _ _ = U1
    restore f = fst (f Proxy)

instance HApplicative c => SymbolicData (Proxy (c :: (Type -> Type) -> Type)) where
    type Context (Proxy c) = c
    type Support (Proxy c) = Proxy c
    type Layout (Proxy c) = U1
    type Payload (Proxy c) = U1

    arithmetize _ _ = hpure U1
    payload _ _ = U1
    restore _ = Proxy

instance
    ( SymbolicData x
    , SymbolicData y
    , HApplicative (Context x)
    , Context x ~ Context y
    , Support x ~ Support y
    ) => SymbolicData (x, y) where

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

instance
    ( SymbolicData x
    , Package (Context x)
    , KnownNat n
    ) => SymbolicData (Vector n x) where

    type Context (Vector n x) = Context x
    type Support (Vector n x) = Support x
    type Layout (Vector n x) = Vector n :.: Layout x
    type Payload (Vector n x) = Vector n :.: Payload x

    arithmetize xs s = pack (flip arithmetize s <$> xs)
    payload xs s = Comp1 (flip payload s <$> xs)
    restore f = tabulate (\i -> restore (bimap (hmap (ix i)) (ix i) . f))
      where ix i = flip index i . unComp1

instance SymbolicData f => SymbolicData (x -> f) where
    type Context (x -> f) = Context f
    type Support (x -> f) = (x, Support f)
    type Layout (x -> f) = Layout f
    type Payload (x -> f) = Payload f

    arithmetize f (x, i) = arithmetize (f x) i
    payload f (x, i) = payload (f x) i
    restore f x = restore (f . (x,))

class GSymbolicData u where
    type GContext u :: (Type -> Type) -> Type
    type GSupport u :: Type
    type GLayout u :: Type -> Type
    type GPayload u :: Type -> Type

    garithmetize :: u x -> GSupport u -> GContext u (GLayout u)
    gpayload :: u x -> GSupport u -> GPayload u (WitnessField (GContext u))
    grestore ::
      GContext u ~ c =>
      (GSupport u -> (c (GLayout u), GPayload u (WitnessField c))) -> u x

instance
    ( GSymbolicData u
    , GSymbolicData v
    , HApplicative (GContext u)
    , GContext u ~ GContext v
    , GSupport u ~ GSupport v
    ) => GSymbolicData (u :*: v) where

    type GContext (u :*: v) = GContext u
    type GSupport (u :*: v) = GSupport u
    type GLayout (u :*: v) = GLayout u :*: GLayout v
    type GPayload (u :*: v) = GPayload u :*: GPayload v

    garithmetize (a :*: b) = hliftA2 (:*:) <$> garithmetize a <*> garithmetize b
    gpayload (a :*: b) = (:*:) <$> gpayload a <*> gpayload b
    grestore f =
      grestore (bimap (hmap fstP) fstP . f)
      :*: grestore (bimap (hmap sndP) sndP . f)

instance GSymbolicData f => GSymbolicData (G.M1 i c f) where
    type GContext (G.M1 i c f) = GContext f
    type GSupport (G.M1 i c f) = GSupport f
    type GLayout (G.M1 i c f) = GLayout f
    type GPayload (G.M1 i c f) = GPayload f
    garithmetize (G.M1 a) = garithmetize a
    gpayload (G.M1 a) = gpayload a
    grestore f = G.M1 (grestore f)

instance SymbolicData x => GSymbolicData (G.Rec0 x) where
    type GContext (G.Rec0 x) = Context x
    type GSupport (G.Rec0 x) = Support x
    type GLayout (G.Rec0 x) = Layout x
    type GPayload (G.Rec0 x) = Payload x
    garithmetize (G.K1 x) = arithmetize x
    gpayload (G.K1 x) = payload x
    grestore f = G.K1 (restore f)
