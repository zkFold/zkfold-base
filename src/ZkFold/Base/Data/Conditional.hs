module ZkFold.Base.Data.Conditional (
    GeneralizedConditional (..)
) where

import           Control.Monad.State                         (evalState)
import           Prelude                                     hiding (Num(..), Bool, (/))
import qualified Prelude                                     as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Data.Bool                       (Bool (..), GeneralizedBoolean (..))
import           ZkFold.Base.Protocol.Arithmetization.R1CS   (R1CS, Arithmetizable (..))

class GeneralizedBoolean b => GeneralizedConditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance GeneralizedConditional Haskell.Bool a where
    bool f t b = if b then t else f

instance Prime p => GeneralizedConditional (Bool (Zp p)) x where
    bool f t b = if b == true then t else f

instance Arithmetizable a x =>
        GeneralizedConditional (Bool (R1CS a)) x where
    bool brFalse brTrue (Bool b) = 
        let f' = evalState (arithmetize brFalse) mempty
            t' = evalState (arithmetize brTrue) mempty
        in restore $ zipWith (\f t -> b * t + (one - b) * f) f' t'