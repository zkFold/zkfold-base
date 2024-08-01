{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC.Type where

import           Data.Kind                        (Type)
import           Data.Typeable                    (Proxy (..), TypeRep, Typeable, typeOf)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Compiler         (SymbolicData (..))

data SomeType a where
    NoType         :: SomeType a
    AnyType        :: SomeType a
    AnyBuiltinType :: SomeType a
    SomeSym        :: SomeSymbolic a -> SomeType a
    SomeFunction   :: SomeType a -> SomeType a -> SomeType a

instance Eq (SomeType a) where
    NoType == NoType                         = True
    AnyType == AnyType                       = True
    AnyBuiltinType == AnyBuiltinType         = True
    SomeSym x == SomeSym y                   = x == y
    SomeFunction x1 x2 == SomeFunction y1 y2 = x1 == y1 && x2 == y2
    _ == _                                   = False

instance Semigroup (SomeType a) where
    NoType <> t                              = t
    t <> NoType                              = t
    AnyType <> t                             = t
    t <> AnyType                             = t
    AnyBuiltinType <> t                      = t
    t <> AnyBuiltinType                      = t
    SomeSym t1 <> SomeSym t2                 = SomeSym (t1 <> t2)
    SomeFunction t1 t2 <> SomeFunction t3 t4 = SomeFunction (t1 <> t3) (t2 <> t4)
    _ <> _                                   = error "Semigroup (SomeType a): constructor mismatch"

data SomeSymbolic a where
    SomeData  :: forall a (t :: Type) . (Typeable t, SymbolicData a t, KnownNat (TypeSize a t)) => Proxy t -> SomeSymbolic a

getType :: SomeSymbolic a -> TypeRep
getType (SomeData t)  = typeOf t

instance Eq (SomeSymbolic a) where
    SomeData x == SomeData y = typeOf x == typeOf y

instance Semigroup (SomeSymbolic a) where
    SomeData x <> SomeData y
      | typeOf x == typeOf y = SomeData x
      | otherwise = error "Semigroup (SomeSymbolic a): SomeData mismatch"

symToSym :: forall a. SomeSymbolic a -> SomeSymbolic a -> SomeSymbolic a
symToSym (SomeData (_ :: Proxy x)) (SomeData (_ :: Proxy y)) = SomeData (Proxy @(x -> y))

-- TODO: add support for polymorphic types
functionToData :: SomeType a -> SomeType a
functionToData (SomeFunction t1 t2) =
    let t1' = functionToData t1
        t2' = functionToData t2
    in case (t1', t2') of
        (SomeSym x, SomeSym y) -> SomeSym (symToSym x y)
        _                      -> error "functionToData: cannot make a conversion"
functionToData t = t
