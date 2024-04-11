{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC.Type where

import           Data.Kind                (Type)
import           Data.Typeable            (Proxy (..), Typeable, typeOf)
import           Prelude

import           ZkFold.Symbolic.Compiler (Arithmetizable)

data SomeType a where
    NoType         :: SomeType a
    AnyType        :: SomeType a
    AnyBuiltinType :: SomeType a
    SomeData       :: forall a (t :: Type) . (Typeable t, Arithmetizable a t) => Proxy t -> SomeType a
    SomeFunction   :: SomeType a -> SomeType a -> SomeType a

instance Eq (SomeType a) where
    NoType == NoType                         = True
    AnyType == AnyType                       = True
    AnyBuiltinType == AnyBuiltinType         = True
    SomeData x == SomeData y                 = typeOf x == typeOf y
    SomeFunction x1 x2 == SomeFunction y1 y2 = x1 == y1 && x2 == y2
    _ == _                                   = False

instance Semigroup (SomeType a) where
    NoType <> t = t
    t <> NoType = t
    AnyType <> t = t
    t <> AnyType = t
    AnyBuiltinType <> t = t
    t <> AnyBuiltinType = t
    SomeData t1 <> SomeData t2
        | typeOf t1 == typeOf t2 = SomeData t1
        | otherwise = error "Semigroup (SomeType a): SomeData mismatch"
    SomeFunction t1 t2 <> SomeFunction t3 t4 = SomeFunction (t1 <> t3) (t2 <> t4)
    _ <> _ = error "Semigroup (SomeType a): constructor mismatch"

-- TODO: add support for polymorphic types
functionToData :: SomeType a -> SomeType a
functionToData (SomeFunction t1 t2) =
    let t1' = functionToData t1
        t2' = functionToData t2
    in case (t1', t2') of
        (SomeData (_ :: Proxy t1), SomeData (_ :: Proxy t2)) -> SomeData (Proxy @(t1 -> t2))
        _                                                    -> error "functionToData: cannot make a conversion"
functionToData t = t
