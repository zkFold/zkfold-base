{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Data.Ord (Ord (..), Lexicographical (..), circuitGE, circuitGT, getBitsBE) where

import           Control.Monad                                             (foldM)
import qualified Data.Bool                                                 as Haskell
import qualified Data.Zip                                                  as Z
import           Prelude                                                   (type (~), ($))
import qualified Prelude                                                   as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Base.Algebra.Basic.Number                          (Prime)
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit)
import           ZkFold.Symbolic.Data.Bool                                 (Bool (..))
import           ZkFold.Symbolic.Data.Conditional                          (Conditional (..))

-- TODO (Issue #23): add `compare`
class Ord b a where
    (<=) :: a -> a -> b

    (<) :: a -> a -> b

    (>=) :: a -> a -> b

    (>) :: a -> a -> b

    max :: a -> a -> a
    -- max x y = bool @b y x $ x <= y

    min :: a -> a -> a
    -- min x y = bool @b y x $ x >= y

instance Haskell.Ord a => Ord Haskell.Bool a where
    (<=) = (Haskell.<=)

    (<) = (Haskell.<)

    (>=) = (Haskell.>=)

    (>) = (Haskell.>)

    max = Haskell.max

    min = Haskell.min

instance {-# OVERLAPPABLE #-} (Prime p, Haskell.Ord x) => Ord (Bool (Zp p)) x where
    x <= y = Bool $ Haskell.bool zero one (x Haskell.<= y)

    x <  y = Bool $ Haskell.bool zero one (x Haskell.<  y)

    x >= y = Bool $ Haskell.bool zero one (x Haskell.>= y)

    x >  y = Bool $ Haskell.bool zero one (x Haskell.>  y)

    max x y = Haskell.bool x y $ x <= y

    min x y = Haskell.bool x y $ x >= y

newtype Lexicographical a = Lexicographical a
-- ^ A newtype wrapper for easy definition of Ord instances
-- (though not necessarily a most effective one)

deriving newtype instance SymbolicData a x => SymbolicData a (Lexicographical x)

deriving via (Lexicographical (ArithmeticCircuit 1 a))
    instance Arithmetic a => Ord (Bool (ArithmeticCircuit 1 a)) (ArithmeticCircuit 1 a)

-- | Every @SymbolicData@ type can be compared lexicographically.
instance (SymbolicData a x, TypeSize a x ~ 1) => Ord (Bool (ArithmeticCircuit 1 a)) (Lexicographical x) where
    x <= y = y >= x

    x <  y = y > x

    x >= y = circuitGE (getBitsBE x) (getBitsBE y)

    x > y = circuitGT (getBitsBE x) (getBitsBE y)

    max x y = bool @(Bool (ArithmeticCircuit 1 a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit 1 a)) x y $ x > y

getBitsBE :: forall a x . (SymbolicData a x, TypeSize a x ~ 1) => x -> ArithmeticCircuit (NumberOfBits a) a
-- ^ @getBitsBE x@ returns a list of circuits computing bits of @x@, eldest to
-- youngest.
getBitsBE x = let expansion = binaryExpansion $ pieces @a @x x
               in expansion { acOutput = V.reverse $ acOutput expansion }

circuitGE :: forall a n . Arithmetic a => ArithmeticCircuit n a -> ArithmeticCircuit n a -> Bool (ArithmeticCircuit 1 a)
-- ^ Given two lists of bits of equal length, compares them lexicographically.
circuitGE xs ys = Bool $ circuit solve
    where
        solve :: MonadBlueprint i a m => m i
        solve = do
            (_, hasNegOne) <- circuitDelta xs ys
            newAssigned $ \p -> one - p hasNegOne

circuitGT :: forall a n . Arithmetic a => ArithmeticCircuit n a -> ArithmeticCircuit n a -> Bool (ArithmeticCircuit 1 a)
-- ^ Given two lists of bits of equal length, compares them lexicographically.
circuitGT xs ys = Bool $ circuit solve
    where
        solve :: MonadBlueprint i a m => m i
        solve = do
            (hasOne, hasNegOne) <- circuitDelta xs ys
            newAssigned $ \p -> p hasOne * (one - p hasNegOne)

circuitDelta :: forall i a m n . MonadBlueprint i a m => ArithmeticCircuit n a -> ArithmeticCircuit n a -> m (i, i)
circuitDelta xs ys = do
    l <- runCircuit xs
    r <- runCircuit ys
    z1 <- newAssigned (Haskell.const zero)
    z2 <- newAssigned (Haskell.const zero)
    foldM update (z1, z2) $ Z.zip l r
        where
            -- | If @z1@ is set, there was an index i where @xs[i] == 1@ and @ys[i] == 0@ and @xs[j] == ys[j]@ for all j < i.
            -- In this case, no matter what bit states are after this index, @z1@ and @z2@ are not updated.
            --
            --   If @z2@ is set, there was an index i where @xs[i] == 0@ and @ys[i] == 1@ and @xs[j] == ys[j]@ for all j < i.
            -- In the same manner, @z1@ and @z2@ won't be updated afterwards.
            update :: (i, i) -> (i, i) -> m (i, i)
            update (z1, z2) (x, y) = do
                z1' <- newAssigned $ \p -> p z1 + (one - p z1) * (one - p z2) * (one - p y) * p x
                z2' <- newAssigned $ \p -> p z2 + (one - p z1) * (one - p z2) * (one - p x) * p y
                Haskell.return (z1', z2')



