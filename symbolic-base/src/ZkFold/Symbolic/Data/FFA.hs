{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BlockArguments #-}

module ZkFold.Symbolic.Data.FFA (FFA (..)) where

import           Control.DeepSeq                   (NFData)
import           Data.Bool                         (otherwise)
import           Data.Ord                          ((<))
import           Data.Type.Equality                (type (~))
import           GHC.Generics                      (Generic, type (:*:) (..), U1 (..), Par1 (..))
import           Numeric.Natural                   (Natural)
import           Prelude                           (Integer, fromIntegral)
import           Text.Show                         (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Base.Algebra.Basic.Number  (Bezout1, KnownInt (..), KnownNat, Prime, type (*), type (^), value)
import           ZkFold.Symbolic.Class             (Arithmetic, Symbolic (..))
import           ZkFold.Symbolic.Data.Bool         (Bool, BoolType (..))
import           ZkFold.Symbolic.Data.Class        (SymbolicData (..))
import           ZkFold.Symbolic.Data.Combinators  (Ceil, KnownRegisterSize, KnownRegisters)
import           ZkFold.Symbolic.Data.Conditional  (Conditional (..))
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Data.Input        (SymbolicInput (..))
import           ZkFold.Symbolic.Data.UInt         (UInt)
import           ZkFold.Symbolic.Interpreter       (Interpreter (..))
import Data.Proxy (Proxy(..))
import Data.Function (($), const)

type family FFAUIntSize (p :: Natural) (q :: Natural) :: Natural where
  FFAUIntSize p p = 0
  FFAUIntSize p q = NumberOfBits (Zp (Ceil (p * p) q))

type UIntFFA p r c = UInt (FFAUIntSize p (Order (BaseField c))) r c

data FFA p r c = FFA
  { nativeResidue :: FieldElement c
  , uintResidue   :: UIntFFA p r c
  }
  deriving (Generic)

type FFABezout p a = Bezout1 p (2 ^ FFAUIntSize p (Order a))

type KnownFFA p r c =
  ( KnownNat (FFAUIntSize p (Order (BaseField c)))
  , KnownInt (FFABezout p (BaseField c))
  , KnownNat p
  , KnownRegisterSize r
  , KnownRegisters c (FFAUIntSize p (Order (BaseField c))) r)

instance (Symbolic c, KnownFFA p r c) => SymbolicData (FFA p r c)
instance (Symbolic c, KnownFFA p r c) => SymbolicInput (FFA p r c) where
  isValid (FFA nx ux) = isValid (nx, ux) -- TODO: add range check
instance (NFData (FieldElement c), NFData (UIntFFA p r c)) => NFData (FFA p r c)
instance (Symbolic c, KnownFFA p r c, b ~ Bool c) => Conditional b (FFA p r c)
instance (Symbolic c, KnownFFA p r c) => Eq (FFA p r c)
deriving stock instance (Show (FieldElement c), Show (UIntFFA p r c)) =>
  Show (FFA p r c)

instance (Arithmetic a, KnownFFA p r (Interpreter a)) =>
    ToConstant (FFA p r (Interpreter a)) where
  type Const (FFA p r (Interpreter a)) = Zp p
  toConstant (FFA nx ux) =
    let n = fromConstant (toConstant (toConstant nx))
        u = fromConstant (toConstant ux) :: Integer
        -- x = k|a| + n = l*2^s + u
        -- k|a| - l*2^s = u - n
        k = (u - n) * intValue @(FFABezout p a)
     in fromConstant (k * fromConstant (order @a) + n)

instance (Symbolic c, KnownFFA p r c, FromConstant a (Zp p)) =>
    FromConstant a (FFA p r c) where
  fromConstant c =
    let c' = toConstant (fromConstant c :: Zp p)
     in FFA (fromConstant c') (fromConstant c')

instance {-# OVERLAPPING #-} FromConstant (FFA p r c) (FFA p r c)

instance {-# OVERLAPPING #-}
  (Symbolic c, KnownFFA p r c) => Scale (FFA p r c) (FFA p r c)

instance (Symbolic c, KnownFFA p r c) => MultiplicativeSemigroup (FFA p r c) where
  FFA nx ux * FFA ny uy = FFA nr ur
    where
      nd, ns :: FieldElement c
      ud, us :: UIntFFA p r c
      (nd, ud, ns, us) = restore $ const
        ( fromCircuitF (arithmetize (nx, ux, ny, uy) Proxy)
            \((Par1 ni :*: ui) :*: (Par1 nj :*: uj)) -> do
              _
        , (U1 :*: U1) :*: (U1 :*: U1))

instance (Symbolic c, KnownFFA p r c) => Exponent (FFA p r c) Natural where
  x ^ a = x `natPow` (a `mod` (value @p -! 1))

instance (Symbolic c, KnownFFA p r c) => MultiplicativeMonoid (FFA p r c) where
  one = fromConstant (one :: Zp p)

instance (Symbolic c, KnownFFA p r c) => AdditiveSemigroup (FFA p r c) where
  FFA nx ux + FFA ny uy = FFA nr ur

instance (Symbolic c, KnownFFA p r c, Scale a (Zp p)) => Scale a (FFA p r c) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Symbolic c, KnownFFA p r c) => AdditiveMonoid (FFA p r c) where
  zero = fromConstant (zero :: Zp p)

instance (Symbolic c, KnownFFA p r c) => AdditiveGroup (FFA p r c) where
  negate (FFA nx ux) = bool
    (FFA (fromConstant (value @p) - nx) (fromConstant (value @p) - ux))
    (FFA nx ux)
    (nx == zero && ux == zero)

instance (Symbolic c, KnownFFA p r c) => Semiring (FFA p r c)

instance (Symbolic c, KnownFFA p r c) => Ring (FFA p r c)

instance (Symbolic c, KnownFFA p r c, Prime p) => Exponent (FFA p r c) Integer where
  x ^ a
    | neg < pos = finv x ^ neg
    | otherwise = x ^ pos
    where
      pos = fromIntegral (a `mod` fromIntegral (value @p -! 1))
      neg = value @p -! (pos + 1)

instance (Symbolic c, KnownFFA p r c, Prime p) => Field (FFA p r c) where
  finv = _

instance Finite (Zp p) => Finite (FFA p r b) where
  type Order (FFA p r b) = p
