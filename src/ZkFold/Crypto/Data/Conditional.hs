module ZkFold.Crypto.Data.Conditional (
    GeneralizedConditional (..) 
) where

import           Prelude                               hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool               (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Data.Symbolic

class GeneralizedBoolean b => GeneralizedConditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool x y b

    (?) :: b -> a -> a -> a
    (?) = gif

instance GeneralizedConditional Bool a where
    bool t f b = if b then t else f

instance (Symbolic ctx a, FiniteField ctx) => GeneralizedConditional (SymbolicBool ctx) a where
    bool t f (SymbolicBool b) =
        let t' = symbolic' t b
            f' = symbolic' f b
        in symVar $ b * t' + (one - b) * f'