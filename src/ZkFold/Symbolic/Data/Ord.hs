{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Data.Ord (Ord (..), Lexicographical (..), blueprintGE, circuitGE, circuitGT, getBitsBE) where

import           Control.Monad                                             (foldM)
import qualified Data.Bool                                                 as Haskell
import           Data.Foldable                                             (Foldable)
import           Data.Function                                             ((.))
import qualified Data.Zip                                                  as Z
import           GHC.Generics                                              (Par1 (..))
import           Prelude                                                   (type (~), ($))
import qualified Prelude                                                   as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.HFunctor                                 (hmap)
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (..), circuit)
import           ZkFold.Symbolic.Data.Bool                                 (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Conditional                          (Conditional (..))
import           ZkFold.Symbolic.Data.FieldElement                         (FieldElement (..))
import           ZkFold.Symbolic.Interpreter                               (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit                              (newAssigned)

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

toValue :: Interpreter a Par1 -> a
toValue (Interpreter (Par1 v)) = v

fromValue :: a -> Interpreter a Par1
fromValue = Interpreter Haskell.. Par1

instance (Arithmetic a, Haskell.Ord a) => Ord (Bool (Interpreter a)) (Interpreter a Par1) where
    (toValue -> x) <= (toValue -> y) = Haskell.bool false true (x Haskell.<= y)
    (toValue -> x) <  (toValue -> y) = Haskell.bool false true (x Haskell.<  y)
    (toValue -> x) >= (toValue -> y) = Haskell.bool false true (x Haskell.>= y)
    (toValue -> x) >  (toValue -> y) = Haskell.bool false true (x Haskell.>  y)
    (toValue -> x) `max` (toValue -> y) = fromValue $ Haskell.max x y
    (toValue -> x) `min` (toValue -> y) = fromValue $ Haskell.min x y

newtype Lexicographical a = Lexicographical a
-- ^ A newtype wrapper for easy definition of Ord instances
-- (though not necessarily a most effective one)

deriving newtype instance SymbolicData a x => SymbolicData a (Lexicographical x)

deriving via (Lexicographical (ArithmeticCircuit a Par1))
    instance Arithmetic a => Ord (Bool (ArithmeticCircuit a)) (ArithmeticCircuit a Par1)

deriving newtype instance (Arithmetic a, Haskell.Ord a) => Ord (Bool (Interpreter a)) (FieldElement (Interpreter a))
deriving newtype instance Arithmetic a => Ord (Bool (ArithmeticCircuit a)) (FieldElement (ArithmeticCircuit a))

-- | Every @SymbolicData@ type can be compared lexicographically.
instance (SymbolicData a x, TypeSize a x ~ 1) => Ord (Bool (ArithmeticCircuit a)) (Lexicographical x) where
    x <= y = y >= x

    x <  y = y > x

    x >= y = circuitGE (getBitsBE x) (getBitsBE y)

    x > y = circuitGT (getBitsBE x) (getBitsBE y)

    max x y = bool @(Bool (ArithmeticCircuit a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit a)) x y $ x > y

getBitsBE :: forall a x . (SymbolicData a x, TypeSize a x ~ 1) => x -> ArithmeticCircuit a (V.Vector (NumberOfBits a))
-- ^ @getBitsBE x@ returns a list of circuits computing bits of @x@, eldest to
-- youngest.
getBitsBE x = let expansion = binaryExpansion $ hmap (Par1 . V.item) (pieces @a @x x)
               in expansion { acOutput = V.reverse $ acOutput expansion }

circuitGE :: forall a f . (Arithmetic a, Z.Zip f, Foldable f) => ArithmeticCircuit a f -> ArithmeticCircuit a f -> Bool (ArithmeticCircuit a)
-- ^ Given two lists of bits of equal length, compares them lexicographically.
circuitGE xs ys = Bool $ circuit $ do
  is <- runCircuit xs
  js <- runCircuit ys
  blueprintGE is js

blueprintGE :: (MonadBlueprint i a m, Z.Zip f, Foldable f) => f i -> f i -> m i
blueprintGE xs ys = do
  (_, hasNegOne) <- circuitDelta xs ys
  newAssigned $ \p -> one - p hasNegOne

circuitGT :: forall a f . (Arithmetic a, Z.Zip f, Foldable f) => ArithmeticCircuit a f -> ArithmeticCircuit a f -> Bool (ArithmeticCircuit a)
-- ^ Given two lists of bits of equal length, compares them lexicographically.
circuitGT xs ys = Bool $ circuit $ do
  is <- runCircuit xs
  js <- runCircuit ys
  (hasOne, hasNegOne) <- circuitDelta is js
  newAssigned $ \p -> p hasOne * (one - p hasNegOne)

circuitDelta :: forall i a m f . (MonadBlueprint i a m, Z.Zip f, Foldable f) => f i -> f i -> m (i, i)
circuitDelta l r = do
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
