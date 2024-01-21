{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Cardano.UPLC where

import           Control.Monad.State             (MonadState (..))
import           Prelude                         (Eq, Monoid (..), ($), return, error)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Arithmetization (Arithmetizable (..), ArithmeticCircuit)

data BuiltinFunctions
    = AddField
    | MulField

instance (FiniteField a, Eq a, ToBits a) => Arithmetizable a BuiltinFunctions where
    arithmetize AddField = arithmetize @a @(ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a) (+)
    arithmetize MulField = arithmetize @a @(ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a) (*)

    restore = error "restore Builtins: not implemented"

    typeSize = error "typeSize Builtins: not implemented"

-- Based on the November 2022 UPLC spec
data Term fun a where
    Var      :: (Arithmetizable a t) => t -> Term fun a
    LamAbs   :: (Arithmetizable a t) => (t -> Term fun a) -> Term fun a
    Apply    :: (Arithmetizable a t) => (t -> Term fun a) -> Term fun a -> Term fun a
    Force    :: Term fun a -> Term fun a
    Delay    :: Term fun a -> Term fun a
    Constant :: (FromConstant c [ArithmeticCircuit a]) => c -> Term fun a
    Builtin  :: fun -> Term fun a
    Error    :: Term fun a

instance (FiniteField a, Eq a, ToBits a) => Arithmetizable a (Term BuiltinFunctions a) where
    arithmetize (Var x)       = arithmetize x
    arithmetize (LamAbs f)    = arithmetize f
    arithmetize (Apply f x)   = do
        aX <- arithmetize x
        arithmetize (f $ restore aX)
    arithmetize (Force x)     = arithmetize x
    arithmetize (Delay x)     = arithmetize x
    arithmetize (Constant x)  = do
        let vs = fromConstant x :: [ArithmeticCircuit a]
        put $ mconcat vs
        return vs
    arithmetize (Builtin fun) = arithmetize fun
    arithmetize Error         = error "arithmetize Term: Error"

    restore = error "restore Term: not implemented"

    typeSize = error "typeSize Term: not implemented"