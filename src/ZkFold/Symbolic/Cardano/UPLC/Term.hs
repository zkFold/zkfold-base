{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Cardano.UPLC.Term where

import Data.Maybe (fromJust)
import Data.Typeable (Typeable, cast, typeOf)
import ZkFold.Symbolic.Compiler (Arithmetizable)
import Prelude

-- Based on the November 2022 UPLC spec
data Term name fun a where
  Var :: name -> Term name fun a
  LamAbs :: name -> Term name fun a -> Term name fun a
  Apply :: Term name fun a -> Term name fun a -> Term name fun a
  Force :: Term name fun a -> Term name fun a
  Delay :: Term name fun a -> Term name fun a
  Constant :: (Eq c, Typeable c, Arithmetizable a c) => c -> Term name fun a
  Builtin :: fun -> Term name fun a
  Error :: Term name fun a

instance (Eq name, Eq fun) => Eq (Term name fun a) where
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
