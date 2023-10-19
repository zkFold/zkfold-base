module ZkFold.Crypto.Data.Conditional (
    GeneralizedConditional (..)
) where

import           Control.Monad.State                         (evalState)
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

-- TODO: make this instance more general! We need to introduce a function that is inverse to `arithmetize`.
instance Arithmetizable a a Integer (R1CS a t s) =>
        GeneralizedConditional (SymbolicBool (R1CS a a Integer)) (R1CS a t s) where
    bool brFalse brTrue (SymbolicBool b) = 
        let f' = atomic brFalse
            t' = atomic brTrue
            r  = mconcat $ zipWith (\f t -> b * t + (one - b) * f) f' t'
        in evalState current r

instance Arithmetizable a a Integer (SymbolicBool (R1CS a a Integer)) =>
        GeneralizedConditional (SymbolicBool (R1CS a a Integer)) (SymbolicBool (R1CS a a Integer)) where
    bool brFalse brTrue (SymbolicBool b) =
        let SymbolicBool bFalse = brFalse
            SymbolicBool bTrue  = brTrue
        in SymbolicBool $ b * bTrue + (one - b) * bFalse