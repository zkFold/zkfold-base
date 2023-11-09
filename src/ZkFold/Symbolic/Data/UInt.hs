module ZkFold.Symbolic.Data.UInt (
    UInt32(..)
) where

import           Control.Monad.State             (MonadState (..))
import           Prelude                         hiding ((^), Num(..), Bool(..), Ord(..), (/), (&&), (||), not, all, any)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Arithmetization (Arithmetizable (..), ArithmeticCircuit(..), forceZero)
import           ZkFold.Symbolic.Data.Bool       (Bool(..))
import           ZkFold.Symbolic.Data.Ord        (Ord(..))

-- TODO: hide this constructor
newtype UInt32 x = UInt32 x
    deriving (Show, Eq)

instance (FiniteField a, Eq a, ToBits a) => Arithmetizable a (UInt32 (ArithmeticCircuit a)) where
    arithmetize (UInt32 i) = do
        ac <- get
        let two = one + one :: ArithmeticCircuit a
            Bool b = ac >= (two ^ (32 :: Integer))
        put b
        forceZero
        arithmetize i

    restore [ac] = UInt32 $ restore [ac]
    restore _   = error "UInt32: invalid number of values"

    typeSize = 1