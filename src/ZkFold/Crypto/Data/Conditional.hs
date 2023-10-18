module ZkFold.Crypto.Data.Conditional (
    GeneralizedConditional (..)
) where

import           Control.Monad.State                         (MonadState (..), evalState)
import           Prelude                                     hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool                     (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (R1CS, Arithmetizable (..), atomic, current)

class GeneralizedBoolean b => GeneralizedConditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance GeneralizedConditional Bool a where
    bool f t b = if b then t else f

instance Arithmetizable a a Integer (R1CS a t s) =>
        GeneralizedConditional (SymbolicBool (R1CS a a Integer)) (R1CS a t s) where
    bool brFalse brTrue (SymbolicBool b) = flip evalState b $ do
        f' <- atomic <$> (arithmetize brFalse >> get)
        t' <- atomic <$> (arithmetize brTrue >> get)
        put $ mconcat $ zipWith (\f t -> b * t + (one - b) * f) f' t'
        current