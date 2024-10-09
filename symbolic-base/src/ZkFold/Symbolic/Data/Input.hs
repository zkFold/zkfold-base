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
import           Prelude (($), return)
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number (KnownNat, type (+) )
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.MonadCircuit
import ZkFold.Symbolic.Data.ByteString


-- | A class for Symbolic input.
class
    ( SymbolicData d
    , Support d ~ Proxy (Context d)
    , Representable (Layout d)
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
    , KnownNat (TypeSize x)
    , KnownNat (TypeSize x + TypeSize y)
    , Layout x ~ Vector (TypeSize x)
    , Layout y ~ Vector (TypeSize y)
    , SymbolicInput x
    , SymbolicInput y
    ) => SymbolicInput (x, y) where
  isValid (l, r) = isValid l && isValid r

-- instance (
--   Symbolic c
--   , KnownNat n 
--   ) => SymbolicInput (ByteString n c) where
--   isValid (ByteString bits) = Bool $ fromCircuitF bits solve
--     where
--         solve :: forall i m . MonadCircuit i (BaseField c) m => Vector n i -> m (Par1 i)
--         solve v = do
--             let vs = fromVector v
--             return $ Par1 ($ v) vs