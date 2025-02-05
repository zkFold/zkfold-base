{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FFA (FFA (..)) where

import           Control.DeepSeq                   (NFData)
import           Data.Type.Equality                (type (~))
import           GHC.Generics                      (Generic)
import           Numeric.Natural                   (Natural)
import           Prelude                           (Integer)
import           Text.Show                         (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Base.Algebra.Basic.Number  (KnownNat, Prime, type (*))
import           ZkFold.Symbolic.Class             (Arithmetic, Symbolic (..))
import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.Class        (SymbolicData (..))
import           ZkFold.Symbolic.Data.Combinators  (Ceil, KnownRegisterSize, KnownRegisters)
import           ZkFold.Symbolic.Data.Conditional  (Conditional)
import           ZkFold.Symbolic.Data.Eq           (Eq)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Data.Input        (SymbolicInput)
import           ZkFold.Symbolic.Data.UInt         (UInt)
import           ZkFold.Symbolic.Interpreter       (Interpreter (..))

type family FFAUIntSize (p :: Natural) (q :: Natural) :: Natural where
  FFAUIntSize p p = 0
  FFAUIntSize p q = NumberOfBits (Zp (Ceil (p * p) q))

type UIntFFA p r c = UInt (FFAUIntSize p (Order (BaseField c))) r c

data FFA p r c = FFA
  { nativeResidue :: FieldElement c
  , uintResidue   :: UIntFFA p r c
  }
  deriving (Generic)

type KnownFFA p r c =
  ( KnownNat (FFAUIntSize p (Order (BaseField c)))
  , KnownRegisterSize r
  , KnownRegisters c (FFAUIntSize p (Order (BaseField c))) r)

instance (Symbolic c, KnownFFA p r c) => SymbolicData (FFA p r c)
instance (Symbolic c, KnownFFA p r c) => SymbolicInput (FFA p r c)
instance (NFData (FieldElement c), NFData (UIntFFA p r c)) => NFData (FFA p r c)
instance (Symbolic c, KnownFFA p r c, b ~ Bool c) => Conditional b (FFA p r c)
instance (Symbolic c, KnownFFA p r c) => Eq (FFA p r c)
deriving stock instance (Show (FieldElement c), Show (UIntFFA p r c)) =>
  Show (FFA p r c)

instance (Arithmetic a, KnownFFA p r (Interpreter a)) =>
    ToConstant (FFA p r (Interpreter a)) where
  type Const (FFA p r (Interpreter a)) = Zp p
  toConstant (FFA nx ux) =
    let n = toConstant (toConstant nx)
        u = toConstant ux
        -- x = k|a| + n = l*2^s + u
        -- k|a| - l*2^s = u - n
     in fromConstant _

instance (FromConstant a (Zp p), Symbolic c) => FromConstant a (FFA p r c) where
  fromConstant c = _

instance {-# OVERLAPPING #-} FromConstant (FFA p r c) (FFA p r c)

instance {-# OVERLAPPING #-} Symbolic c => Scale (FFA p r c) (FFA p r c)

instance Symbolic c => MultiplicativeSemigroup (FFA p r c) where
  FFA nx ux * FFA ny uy = _

instance Symbolic c => Exponent (FFA p r c) Natural where
  FFA nx ux ^ a = _

instance (Symbolic c, KnownNat p) => MultiplicativeMonoid (FFA p r c) where
  one = fromConstant (one :: Zp p)

instance Symbolic c => AdditiveSemigroup (FFA p r c) where
  FFA nx ux + FFA ny uy = _

instance (Scale a (Zp p), KnownNat p, Symbolic c) => Scale a (FFA p r c) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Symbolic c, KnownNat p) => AdditiveMonoid (FFA p r c) where
  zero = fromConstant (zero :: Zp p)

instance (Symbolic c, KnownNat p) => AdditiveGroup (FFA p r c) where
  negate (FFA nx ux) = _

instance (Symbolic c, KnownNat p) => Semiring (FFA p r c)

instance (Symbolic c, KnownNat p) => Ring (FFA p r c)

instance (Symbolic c, Prime p) => Exponent (FFA p r c) Integer where
  x ^ a = _

instance (Symbolic c, Prime p) => Field (FFA p r c) where
  finv (FFA nx ux) = _

instance Finite (Zp p) => Finite (FFA p r b) where
  type Order (FFA p r b) = p
