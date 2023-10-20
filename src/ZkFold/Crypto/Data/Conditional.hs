module ZkFold.Crypto.Data.Conditional (
    GeneralizedConditional (..)
) where

import           Control.Monad.State                         (evalState)
import           Prelude                                     hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool                     (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (R1CS, Arithmetizable (..))

class GeneralizedBoolean b => GeneralizedConditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance GeneralizedConditional Bool a where
    bool f t b = if b then t else f

instance Arithmetizable a x =>
        GeneralizedConditional (SymbolicBool (R1CS a)) x where
    bool brFalse brTrue (SymbolicBool b) = 
        let f' = evalState (arithmetize brFalse) mempty
            t' = evalState (arithmetize brTrue) mempty
        in restore $ zipWith (\f t -> b * t + (one - b) * f) f' t'