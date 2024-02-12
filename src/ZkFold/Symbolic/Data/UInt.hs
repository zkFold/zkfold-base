{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.UInt (
    UInt32(..)
) where

import           Control.Monad.State             (execState, modify)
import           Prelude                         hiding ((^), Num(..), Bool(..), Ord(..), (/), (&&), (||), not, all, any)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool       (Bool(..))
import           ZkFold.Symbolic.Data.Ord        (Ord(..))

class IntType i x where
    rangeCheck :: x -> x

instance IntType i (Zp a) where
    rangeCheck = id

-- TODO (Issue #18): hide this constructor
-- TODO: change bytes to bits in the name
newtype UInt32 x = UInt32 x
    deriving (Show, Eq)

--------------------------------------------------------------------------------

instance (AdditiveSemigroup (Zp a)) => AdditiveSemigroup (UInt32 (Zp a)) where
    UInt32 x + UInt32 y = UInt32 $ rangeCheck @UInt32 $ x + y

instance (AdditiveMonoid (Zp a)) => AdditiveMonoid (UInt32 (Zp a)) where
    zero = UInt32 zero

instance (AdditiveGroup (Zp a)) => AdditiveGroup (UInt32 (Zp a)) where
    UInt32 x - UInt32 y = UInt32 $ rangeCheck @UInt32 $ x - y

    negate (UInt32 x) = UInt32 $ rangeCheck @UInt32 $ negate x

instance (MultiplicativeSemigroup (Zp a)) => MultiplicativeSemigroup (UInt32 (Zp a)) where
    UInt32 x * UInt32 y = UInt32 $ rangeCheck @UInt32 $ x * y

instance (MultiplicativeMonoid (Zp a)) => MultiplicativeMonoid (UInt32 (Zp a)) where
    one = UInt32 one

--------------------------------------------------------------------------------

instance Arithmetic a => IntType UInt32 (ArithmeticCircuit a) where
    rangeCheck ac =
        let two = one + one :: ArithmeticCircuit a
            Bool b = ac >= (two ^ (32 :: Integer))
        in execState forceZero b

instance Arithmetizable a x => Arithmetizable a (UInt32 x) where
    arithmetize (UInt32 a) = do
        modify (rangeCheck @UInt32)
        arithmetize a

    restore [ac] = UInt32 $ restore [ac]
    restore _   = error "UInt32: invalid number of values"

    typeSize = 1

instance Arithmetic a => AdditiveSemigroup (UInt32 (ArithmeticCircuit a)) where
    UInt32 x + UInt32 y = UInt32 $ rangeCheck @UInt32 $ x + y

instance Arithmetic a => AdditiveMonoid (UInt32 (ArithmeticCircuit a)) where
    zero = UInt32 zero

instance Arithmetic a => AdditiveGroup (UInt32 (ArithmeticCircuit a)) where
    UInt32 x - UInt32 y = UInt32 $ rangeCheck @UInt32 $ x - y

    negate (UInt32 x) = UInt32 $ rangeCheck @UInt32 $ negate x

instance Arithmetic a => MultiplicativeSemigroup (UInt32 (ArithmeticCircuit a)) where
    UInt32 x * UInt32 y = UInt32 $ rangeCheck @UInt32 $ x * y

instance Arithmetic a => MultiplicativeMonoid (UInt32 (ArithmeticCircuit a)) where
    one = UInt32 one
