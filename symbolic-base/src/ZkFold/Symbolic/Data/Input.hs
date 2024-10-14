{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Input (
    SymbolicInput (..)
) where

import           Data.Type.Equality               (type (~))
import           Data.Typeable                    (Proxy (..))
import           Data.Functor
import           Data.Functor.Rep                 (Representable )
import           GHC.Generics                     (Par1 (..))
import           Prelude (($), const)
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number (KnownNat)
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.MonadCircuit
import ZkFold.Symbolic.Data.ByteString
import Data.Traversable (for)
import Data.Foldable (foldlM)
import ZkFold.Base.Data.ByteString (Binary)
import Control.Monad.Representable.Reader (Rep)
import Data.Ord (Ord)
import ZkFold.Symbolic.Data.UInt
import ZkFold.Symbolic.Data.Combinators


-- | A class for Symbolic input.
class
    ( SymbolicData d
    , Support d ~ Proxy (Context d)
    , Representable (Layout d)
    , Binary (Rep (Layout d))
    , Ord (Rep (Layout d))
    ) => SymbolicInput d where
    isValid :: d -> Bool (Context d)


instance Symbolic c => SymbolicInput (Bool c) where
  isValid (Bool b) = Bool $ fromCircuitF b $
      \(Par1 v) -> Par1 <$> newAssigned (($ v) * (one - ($ v))) -- проверка, что i -- это 0 или 1


instance Symbolic c => SymbolicInput (c Par1) where
  isValid _ = true


instance Symbolic c => SymbolicInput (Proxy c) where
  isValid _ = true

instance (
    Symbolic (Context x)
    , Support x ~ Proxy (Context x)
    , Context x ~ Context y
    , SymbolicInput x
    , SymbolicInput y
    ) => SymbolicInput (x, y) where
  isValid (l, r) = isValid l && isValid r

instance (
  Symbolic c
  , KnownNat n 
  ) => SymbolicInput (ByteString n c) where
  isValid (ByteString bits) = Bool $ fromCircuitF bits solve
    where
        solve :: MonadCircuit i (BaseField c) m => Vector n i -> m (Par1 i)
        solve v = do
            let vs = fromVector v
            ys <- for vs $ \i -> newAssigned (\p -> p i * (one - p i))
            i' <- helper ys
            Par1 <$> newAssigned (\w -> one - w i')
        
        helper :: MonadCircuit i a m => [i] -> m i
        helper xs = case xs of
            []       -> newAssigned (const zero)
            (b : bs) -> foldlM (\a i -> newAssigned (\x -> let xa = x a in x i + xa )) b bs

-- instance (
--   Symbolic c
--   , KnownNat (NumberOfRegisters (BaseField c) n r)
--   ) => SymbolicInput (UInt n r c) where
--   isValid (UInt bits) = Bool $ fromCircuitF bits solve
--     where
--         solve :: MonadCircuit i (BaseField c) m => Vector (NumberOfRegisters (BaseField c) n r) i -> m (Par1 i)
--         solve v = do
--             let vs = fromVector v
--             ys <- for vs $ \i -> newAssigned (\p -> p i * (one - p i))
--             i' <- helper ys
--             Par1 <$> newAssigned (\w -> one - w i')
        
--         helper :: MonadCircuit i a m => [i] -> m i
--         helper xs = case xs of
--             []       -> newAssigned (const zero)
--             (b : bs) -> foldlM (\a i -> newAssigned (\x -> let xa = x a in x i + xa )) b bs
