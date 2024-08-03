{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Cardano.UPLC.Term where

import           Data.Maybe                       (fromJust)
import           Data.Typeable                    (Typeable, cast, typeOf)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Data.Class

-- Based on the November 2022 UPLC spec
data Term name fun c where
    Var       :: name -> Term name fun c
    LamAbs    :: name -> Term name fun c -> Term name fun c
    Apply     :: Term name fun c -> Term name fun c -> Term name fun c
    Force     :: Term name fun c -> Term name fun c
    Delay     :: Term name fun c -> Term name fun c
    Constant  :: (Eq x, Typeable x, SymbolicData c x, KnownNat (TypeSize c x)) => x -> Term name fun c
    Builtin   :: fun -> Term name fun c
    Error     :: Term name fun c

instance (Eq name, Eq fun) => Eq (Term name fun c) where
    Var x == Var y = x == y
    LamAbs x f == LamAbs y g = x == y && f == g
    Apply f x == Apply g y = f == g && x == y
    Force x == Force y = x == y
    Delay x == Delay y = x == y
    Constant x == Constant y
        | typeOf x == typeOf y = x == fromJust (cast y)
        | otherwise = False
    Builtin x == Builtin y = x == y
    Error == Error = True
    _ == _ = False
