module ZkFold.Crypto.Data.Conditional (
    GeneralizedConditional (..)
) where

import           Control.Monad.State                         (MonadState (..), evalState)
import           Prelude                                     hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool                     (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (atomic, R1CS, current, Arithmetization (..))

class GeneralizedBoolean b => GeneralizedConditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance GeneralizedConditional Bool a where
    bool f t b = if b then t else f

instance (FiniteField a, Eq a, ToBits a, Arithmetization a a Integer (R1CS a t s)) =>
        GeneralizedConditional (SymbolicBool (R1CS a a Integer)) (R1CS a t s) where
    bool brFalse brTrue (SymbolicBool b) = flip evalState b $ do
        f' <- atomic <$> (merge brFalse >> get)
        t' <- atomic <$> (merge brTrue >> get)
        put $ mconcat $ zipWith (\f t -> b * t + (one - b) * f) f' t'
        current