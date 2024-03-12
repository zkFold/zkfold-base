{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Data.UInt (
    UInt(..)
) where

import           Data.Foldable                   (for_)
import           Data.Traversable                (for)
import           GHC.TypeNats                    (Natural)
import           Prelude                         hiding (Bool (..), Num (..), Ord (..), all, any, not, (&&), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool       (Bool (..))
import           ZkFold.Symbolic.Data.Ord        (Ord (..))

class IntType i x where
    rangeCheck :: x -> x

instance IntType i (Zp a) where
    rangeCheck = id

-- TODO (Issue #18): hide this constructor
newtype UInt (n :: Natural) x = UInt x
    deriving (Show, Eq)

--------------------------------------------------------------------------------

instance (AdditiveSemigroup (Zp a)) => AdditiveSemigroup (UInt n (Zp a)) where
    UInt x + UInt y = UInt $ rangeCheck @UInt $ x + y

instance (AdditiveMonoid (Zp a)) => AdditiveMonoid (UInt n (Zp a)) where
    zero = UInt zero

instance (AdditiveGroup (Zp a)) => AdditiveGroup (UInt n (Zp a)) where
    UInt x - UInt y = UInt $ rangeCheck @UInt $ x - y

    negate (UInt x) = UInt $ rangeCheck @UInt $ negate x

instance (MultiplicativeSemigroup (Zp a)) => MultiplicativeSemigroup (UInt n (Zp a)) where
    UInt x * UInt y = UInt $ rangeCheck @UInt $ x * y

instance (MultiplicativeMonoid (Zp a)) => MultiplicativeMonoid (UInt n (Zp a)) where
    one = UInt one

--------------------------------------------------------------------------------

instance Arithmetic a => IntType UInt (ArithmeticCircuit a) where
    rangeCheck ac = circuit $ do
        let two = one + one
            Bool b = ac >= (two ^ (32 :: Integer))
        i <- runCircuit b
        constraint (\x -> x i)
        return i

instance Arithmetizable a x => Arithmetizable a (UInt n x) where
    arithmetize (UInt a) = do
        let cs = circuits (arithmetize a)
        for_ cs $ runCircuit . rangeCheck @UInt
        for cs runCircuit

    restore [ac] = UInt $ restore [ac]
    restore _    = error "UInt32: invalid number of values"

    typeSize = 1

instance Arithmetic a => AdditiveSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt x + UInt y = UInt $ rangeCheck @UInt $ x + y

instance Arithmetic a => AdditiveMonoid (UInt n (ArithmeticCircuit a)) where
    zero = UInt zero

instance Arithmetic a => AdditiveGroup (UInt n (ArithmeticCircuit a)) where
    UInt x - UInt y = UInt $ rangeCheck @UInt $ x - y

    negate (UInt x) = UInt $ rangeCheck @UInt $ negate x

instance Arithmetic a => MultiplicativeSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt x * UInt y = UInt $ rangeCheck @UInt $ x * y

instance Arithmetic a => MultiplicativeMonoid (UInt n (ArithmeticCircuit a)) where
    one = UInt one
