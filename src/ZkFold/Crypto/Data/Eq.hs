module ZkFold.Crypto.Data.Eq (
    GeneralizedEq(..)
) where

import           Control.Monad.State                         (evalState)
import           Prelude                                     hiding (Num(..), (/=), (==), (/), product)
import qualified Prelude                                     as Haskell hiding (product)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool                     (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (Arithmetizable (..), R1CS)

class GeneralizedBoolean b => GeneralizedEq b a where
    (==) :: a -> a -> b

    (/=) :: a -> a -> b

instance Eq a => GeneralizedEq Bool a where
    x == y = x Haskell.== y
    x /= y = x Haskell./= y

instance Arithmetizable a x =>
        GeneralizedEq (SymbolicBool (R1CS a)) x where
    x == y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
            bs = map (\z -> one - z / z) zs
        in SymbolicBool $ product bs

    x /= y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
            bs = map (\z -> one - z / z) zs
        in SymbolicBool $ one - product bs