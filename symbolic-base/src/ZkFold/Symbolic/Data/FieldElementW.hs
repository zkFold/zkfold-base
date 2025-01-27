{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FieldElementW where

import           Data.Function                     (const, ($), (.))
import           Data.Proxy                        (Proxy (..))
import           Data.Tuple                        (snd)
import           GHC.Generics                      (Par1 (..), U1 (..))
import qualified Prelude                           as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number  (KnownNat, Log2, Natural, type (+), type (-))
import           ZkFold.Base.Control.HApplicative  (hunit)
import           ZkFold.Base.Data.Vector           (Vector)
import           ZkFold.Symbolic.Class             (Symbolic (..), embedW)
import           ZkFold.Symbolic.Data.Bool         (Bool (..), BoolType (false), false, true)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional  (Conditional (..))
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (..))
import           ZkFold.Symbolic.Data.Input        (SymbolicInput (..))

newtype FieldElementW c = FieldElementW { fromFieldElementW :: WitnessField c }

constrainFieldElement :: Symbolic c => FieldElementW c -> FieldElement c
constrainFieldElement = FieldElement . embedW . Par1 . fromFieldElementW

unconstrainFieldElement :: Symbolic c => FieldElement c -> FieldElementW c
unconstrainFieldElement = FieldElementW . unPar1 . witnessF . fromFieldElement

deriving newtype instance P.Show (WitnessField c) => P.Show (FieldElementW c)
deriving newtype instance P.Eq (WitnessField c) => P.Eq (FieldElementW c)

instance Symbolic c => SymbolicData (FieldElementW c) where
  type Context (FieldElementW c) = c
  type Support (FieldElementW c) = Proxy c
  type Layout (FieldElementW c) = U1
  type Payload (FieldElementW c) = Par1

  arithmetize _ _ = hunit
  payload = const . Par1 . fromFieldElementW
  restore = FieldElementW . unPar1 . snd . ($ Proxy)

instance Symbolic c => SymbolicInput (FieldElementW c) where
  isValid = const true

instance (Symbolic c, P.Eq (WitnessField c)) => Eq (Bool c) (FieldElementW c) where
  FieldElementW x == FieldElementW y = if x P.== y then true else false
  FieldElementW x /= FieldElementW y = if x P./= y then true else false

instance Symbolic c => Conditional (Bool c) (FieldElementW c) where
  bool (FieldElementW onFalse) (FieldElementW onTrue) (Bool (witnessF -> Par1 b)) =
    FieldElementW $ onTrue * b + (one - b) * onFalse

instance {-# OVERLAPPING #-} FromConstant (FieldElementW c) (FieldElementW c)
deriving newtype instance (Symbolic c, FromConstant k (WitnessField c)) => FromConstant k (FieldElementW c)
deriving newtype instance Symbolic c => ToConstant (FieldElementW c)
instance {-# OVERLAPPING #-} Symbolic c => Scale (FieldElementW c) (FieldElementW c)
deriving newtype instance (Symbolic c, Scale k (WitnessField c)) => Scale k (FieldElementW c)
deriving newtype instance Symbolic c => AdditiveSemigroup (FieldElementW c)
deriving newtype instance Symbolic c => AdditiveMonoid (FieldElementW c)
deriving newtype instance Symbolic c => AdditiveGroup (FieldElementW c)
deriving newtype instance Symbolic c => MultiplicativeSemigroup (FieldElementW c)
instance Symbolic c => Exponent (FieldElementW c) Natural where
  (^) = natPow
deriving newtype instance Symbolic c => MultiplicativeMonoid (FieldElementW c)
deriving newtype instance Symbolic c => Semiring (FieldElementW c)
deriving newtype instance Symbolic c => Ring (FieldElementW c)
instance Symbolic c => Exponent (FieldElementW c) P.Integer where
  (^) = intPowF
deriving newtype instance Symbolic c => Field (FieldElementW c)
deriving newtype instance
  ( Symbolic c
  , KnownNat (Order (WitnessField c))
  , KnownNat (Log2 (Order (WitnessField c) - 1) + 1)
  ) => Finite (FieldElementW c)
-- TODO: Optimize this instance
instance Symbolic c => BinaryExpansion (FieldElementW c) where
  type Bits (FieldElementW c) = c (Vector (NumberOfBits (BaseField c)))
  binaryExpansion = embedW . witnessF . binaryExpansion . constrainFieldElement
  fromBinary = unconstrainFieldElement . fromBinary
