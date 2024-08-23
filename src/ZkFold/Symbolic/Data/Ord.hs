{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Data.Ord (Ord (..), Lexicographical (..), blueprintGE, bitwiseGE, bitwiseGT, getBitsBE) where

import           Control.Monad                                          (foldM)
import qualified Data.Bool                                              as Haskell
import           Data.Data                                              (Proxy (..))
import           Data.Foldable                                          (Foldable, toList)
import           Data.Function                                          ((.))
import           Data.Functor                                           ((<$>))
import qualified Data.Zip                                               as Z
import           GHC.Generics                                           (Par1 (..))
import           Prelude                                                (type (~), ($))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.HFunctor                              (hmap)
import qualified ZkFold.Base.Data.Vector                                as V
import           ZkFold.Base.Data.Vector                                (unsafeToVector)
import           ZkFold.Symbolic.Class                                  (Symbolic (BaseField, symbolicF), symbolic2F)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (expansion)
import           ZkFold.Symbolic.Data.Bool                              (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional                       (Conditional (..))
import           ZkFold.Symbolic.MonadCircuit                           (MonadCircuit, newAssigned)

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

newtype Lexicographical a = Lexicographical a
-- ^ A newtype wrapper for easy definition of Ord instances
-- (though not necessarily a most effective one)

deriving newtype instance SymbolicData a => SymbolicData (Lexicographical a)

-- | Every @SymbolicData@ type can be compared lexicographically.
instance
    ( Symbolic c
    , SymbolicData x
    , Context x ~ c
    , Support x ~ Proxy c
    , TypeSize x ~ 1
    ) => Ord (Bool c) (Lexicographical x) where

    x <= y = y >= x

    x <  y = y > x

    x >= y = bitwiseGE (getBitsBE x) (getBitsBE y)

    x > y = bitwiseGT (getBitsBE x) (getBitsBE y)

    max x y = bool @(Bool c) x y $ x < y

    min x y = bool @(Bool c) x y $ x > y

getBitsBE ::
  forall c x .
  (Symbolic c, SymbolicData x, Context x ~ c, Support x ~ Proxy c, TypeSize x ~ 1) =>
  x -> c (V.Vector (NumberOfBits (BaseField c)))
-- ^ @getBitsBE x@ returns a list of circuits computing bits of @x@, eldest to
-- youngest.
getBitsBE x =
  hmap unsafeToVector
    $ symbolicF (pieces x Proxy) (binaryExpansion . V.item)
      $ expansion (numberOfBits @(BaseField c)) . V.item

bitwiseGE :: forall c f . (Symbolic c, Z.Zip f, Foldable f) => c f -> c f -> Bool c
-- ^ Given two lists of bits of equal length, compares them lexicographically.
bitwiseGE xs ys = Bool $
  symbolic2F xs ys
    (\us vs -> Par1 $ Haskell.bool zero one (toList us Haskell.>= toList vs))
    $ \is js -> Par1 <$> blueprintGE is js

blueprintGE :: (MonadCircuit i a m, Z.Zip f, Foldable f) => f i -> f i -> m i
blueprintGE xs ys = do
  (_, hasNegOne) <- circuitDelta xs ys
  newAssigned $ \p -> one - p hasNegOne

bitwiseGT :: forall c f . (Symbolic c, Z.Zip f, Foldable f) => c f -> c f -> Bool c
-- ^ Given two lists of bits of equal length, compares them lexicographically.
bitwiseGT xs ys = Bool $
  symbolic2F xs ys
    (\us vs -> Par1 $ Haskell.bool zero one (toList us Haskell.> toList vs))
    $ \is js -> do
      (hasOne, hasNegOne) <- circuitDelta is js
      Par1 <$> newAssigned (\p -> p hasOne * (one - p hasNegOne))

circuitDelta :: forall i a m f . (MonadCircuit i a m, Z.Zip f, Foldable f) => f i -> f i -> m (i, i)
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
