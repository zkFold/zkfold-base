module ZkFold.Base.Data.Eq (
    GeneralizedEq(..),
    elem
) where

import           Control.Monad.State                         (evalState)
import           Data.Bool                                   (bool)
import           Prelude                                     hiding (Num(..), Bool, (/=), (==), (/), any, product, elem)
import qualified Prelude                                     as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Data.Bool                       (Bool (..), GeneralizedBoolean, any)
import           ZkFold.Base.Protocol.Arithmetization.R1CS   (Arithmetizable (..), R1CS)

class GeneralizedBoolean b => GeneralizedEq b a where
    (==) :: a -> a -> b

    (/=) :: a -> a -> b

instance Eq a => GeneralizedEq Haskell.Bool a where
    x == y = x Haskell.== y
    x /= y = x Haskell./= y

instance (Prime p, Haskell.Eq x) => GeneralizedEq (Bool (Zp p)) x where
    x == y = Bool $ bool zero one (x Haskell.== y)
    x /= y = Bool $ bool zero one (x Haskell./= y)

instance Arithmetizable a x =>
        GeneralizedEq (Bool (R1CS a)) x where
    x == y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
            bs = map (\z -> one - z / z) zs
        in Bool $ product bs

    x /= y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
            bs = map (\z -> one - z / z) zs
        in Bool $ one - product bs

elem :: GeneralizedEq b a => a -> [a] -> b
elem x = any (== x)