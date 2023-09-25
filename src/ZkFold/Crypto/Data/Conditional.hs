module ZkFold.Crypto.Data.Conditional (
    GeneralizedConditional (..) 
) where

import           Control.Monad.State                   (MonadState (..), execState)
import           Prelude                               hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool               (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Data.Symbolic

class GeneralizedBoolean b => GeneralizedConditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance GeneralizedConditional Bool a where
    bool f t b = if b then t else f

instance (Symbolic ctx a, FiniteField ctx) => GeneralizedConditional (SymbolicBool ctx) a where
    bool f t (SymbolicBool b) = extract $ flip execState b $ do
        f' <- merge f
        t' <- merge t
        put $ b * t' + (one - b) * f'