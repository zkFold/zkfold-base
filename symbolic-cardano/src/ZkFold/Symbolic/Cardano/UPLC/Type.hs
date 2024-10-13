{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Cardano.UPLC.Type where

import           Data.Typeable              (Proxy (..), TypeRep, Typeable, typeOf)
import           Prelude

import           ZkFold.Symbolic.Data.Class (SymbolicData (..))

data SomeType c where
    NoType         :: SomeType c
    AnyType        :: SomeType c
    AnyBuiltinType :: SomeType c
    SomeSym        :: SomeSymbolic c -> SomeType c
    SomeFunction   :: SomeType c -> SomeType c -> SomeType c

instance Eq (SomeType c) where
    NoType == NoType                         = True
    AnyType == AnyType                       = True
    AnyBuiltinType == AnyBuiltinType         = True
    SomeSym x == SomeSym y                   = x == y
    SomeFunction x1 x2 == SomeFunction y1 y2 = x1 == y1 && x2 == y2
    _ == _                                   = False

instance Semigroup (SomeType c) where
    NoType <> t                              = t
    t <> NoType                              = t
    AnyType <> t                             = t
    t <> AnyType                             = t
    AnyBuiltinType <> t                      = t
    t <> AnyBuiltinType                      = t
    SomeSym t1 <> SomeSym t2                 = SomeSym (t1 <> t2)
    SomeFunction t1 t2 <> SomeFunction t3 t4 = SomeFunction (t1 <> t3) (t2 <> t4)
    _ <> _                                   = error "Semigroup (SomeType a): constructor mismatch"

data SomeSymbolic c where
    SomeData :: (Typeable t, SymbolicData t, Context t ~ c) => Proxy t -> SomeSymbolic c

getType :: SomeSymbolic c -> TypeRep
getType (SomeData t)  = typeOf t

instance Eq (SomeSymbolic c) where
    SomeData x == SomeData y = typeOf x == typeOf y

instance Semigroup (SomeSymbolic c) where
    SomeData x <> SomeData y
      | typeOf x == typeOf y = SomeData x
      | otherwise = error "Semigroup (SomeSymbolic a): SomeData mismatch"

symToSym :: SomeSymbolic c -> SomeSymbolic c -> SomeSymbolic c
symToSym (SomeData (_ :: Proxy x)) (SomeData (_ :: Proxy y)) = SomeData (Proxy @(x -> y))

-- TODO: add support for polymorphic types
functionToData :: SomeType c -> SomeType c
functionToData (SomeFunction t1 t2) =
    let t1' = functionToData t1
        t2' = functionToData t2
    in case (t1', t2') of
        (SomeSym x, SomeSym y) -> SomeSym (symToSym x y)
        _                      -> error "functionToData: cannot make a conversion"
functionToData t = t
