{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FFA (FFA (..), KnownFFA) where

import           Control.DeepSeq                   (NFData)
import           Control.Monad                     (Monad (..))
import           Data.Bool                         (otherwise)
import           Data.Function                     (const, ($))
import           Data.Functor.Rep                  (Representable (..))
import           Data.Ord                          ((<))
import           Data.Proxy                        (Proxy (..))
import           Data.Traversable                  (Traversable (..))
import           Data.Type.Equality                (type (~))
import           GHC.Generics                      (Generic, Par1 (..), U1 (..), type (:*:) (..))
import           Numeric.Natural                   (Natural)
import           Prelude                           (Integer)
import qualified Prelude
import           Text.Show                         (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Base.Algebra.Basic.Number  (KnownNat, Prime, type (*), value)
import           ZkFold.Base.Data.Vector           (Vector)
import           ZkFold.Symbolic.Class             (Arithmetic, Symbolic (..))
import           ZkFold.Symbolic.Data.Bool         (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Class        (SymbolicData (..))
import           ZkFold.Symbolic.Data.Combinators  (Ceil, KnownRegisterSize, KnownRegisters, NumberOfRegisters)
import           ZkFold.Symbolic.Data.Conditional  (Conditional (..))
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Data.Input        (SymbolicInput (..))
import           ZkFold.Symbolic.Data.UInt         (UInt, natural, register)
import           ZkFold.Symbolic.Interpreter       (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit      (MonadCircuit (..), Witness (..), ResidueField (..))
import Data.Tuple (snd)
import Data.Bits (Bits(..))

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

bezoutFFA ::
  forall p a. (KnownNat p, KnownNat (FFAUIntSize p (Order a))) => Integer
bezoutFFA =
  snd $ eea ( 1 `shiftL` Prelude.fromIntegral (value @(FFAUIntSize p (Order a)))
            , fromConstant $ value @p) (1, 0)
  where
    eea :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
    eea (g, 0) (s, _) = (g, s)
    eea (q, r) (s, t) = eea (r, q `mod` r) (t, s - (q `div` r) * t)

instance (Arithmetic a, KnownFFA p r (Interpreter a)) =>
    ToConstant (FFA p r (Interpreter a)) where
  type Const (FFA p r (Interpreter a)) = Zp p
  toConstant (FFA nx ux) =
    let n = fromConstant (toConstant (toConstant nx))
        u = fromConstant (toConstant ux) :: Integer
        -- x = k|a| + n = l*2^s + u
        -- k|a| - l*2^s = u - n
        k = (u - n) * bezoutFFA @p @a
     in fromConstant (k * fromConstant (order @a) + n)

instance (Symbolic c, KnownFFA p r c, FromConstant a (Zp p)) =>
    FromConstant a (FFA p r c) where
  fromConstant c =
    let c' = toConstant (fromConstant c :: Zp p)
     in FFA (fromConstant c') (fromConstant c')

instance {-# OVERLAPPING #-} FromConstant (FFA p r c) (FFA p r c)

instance {-# OVERLAPPING #-}
  (Symbolic c, KnownFFA p r c) => Scale (FFA p r c) (FFA p r c)

valueFFA ::
  forall p r c i a.
  (Symbolic c, KnownFFA p r c, Witness i (WitnessField c), a ~ BaseField c) =>
  i -> Vector (NumberOfRegisters a (FFAUIntSize p (Order a)) r) i ->
  IntegralOf (WitnessField c)
valueFFA ni ui =
  let n = toIntegral (at ni :: WitnessField c)
      u = natural @c @(FFAUIntSize p (Order a)) @r ui
      k = (u - n) * fromConstant (bezoutFFA @p @a)
   in k * fromConstant (order @a) + n

layoutFFA ::
  forall p r c a w.
  (Symbolic c, KnownFFA p r c, a ~ BaseField c, w ~ WitnessField c) =>
  IntegralOf w ->
  (Par1 :*: Vector (NumberOfRegisters a (FFAUIntSize p (Order a)) r)) w
layoutFFA c =
  Par1 (fromIntegral c)
  :*: tabulate (register @c @(FFAUIntSize p (Order a)) @r c)

instance (Symbolic c, KnownFFA p r c) => MultiplicativeSemigroup (FFA p r c) where
  FFA nx ux * FFA ny uy = FFA nr ur
    where
      p :: FromConstant Natural a => a
      p = fromConstant (value @p)
      -- | Computes unconstrained \(d = ab div p\) and \(m = ab mod p\)
      nd, nm :: FieldElement c
      ud, um :: UIntFFA p r c
      (nd, ud, nm, um) = restore $ const
        ( fromCircuitF (arithmetize (nx, ux, ny, uy) Proxy)
            \((Par1 ni :*: ui) :*: (Par1 nj :*: uj)) -> do
              let prd = valueFFA @p @r @c ni ui * valueFFA @p @r @c nj uj
              traverse unconstrained
                  $ layoutFFA @p @r @c (prd `div` p)
                  :*: layoutFFA @p @r @c (prd `mod` p)
        , (U1 :*: U1) :*: (U1 :*: U1))
      -- | Constraints:
      -- * UInt registers are indeed registers;
      -- * m < p;
      -- * equation holds modulo basefield;
      -- * equation holds modulo 2^k.
      Bool ck = isValid (ud, FFA @p nm um)
                && (nx * ny == nd * p + nm)
                && (ux * uy == ud * p + um)
      -- | Sew constraints into result.
      (nr, ur) = restore $ const
        ( fromCircuitF (arithmetize (nm, um, ck) Proxy)
            \(ni :*: ui :*: Par1 b) -> do
              constraint (($ b) - one)
              return (ni :*: ui)
        , U1 :*: U1)

instance (Symbolic c, KnownFFA p r c) => Exponent (FFA p r c) Natural where
  x ^ a = x `natPow` (a `mod` (value @p -! 1))

instance (Symbolic c, KnownFFA p r c) => MultiplicativeMonoid (FFA p r c) where
  one = fromConstant (one :: Zp p)

instance (Symbolic c, KnownFFA p r c) => AdditiveSemigroup (FFA p r c) where
  FFA nx ux + FFA ny uy = FFA nr ur
    where
      p :: FromConstant Natural a => a
      p = fromConstant (value @p)
      -- | Computes unconstrained \(d = ab div p\) and \(m = ab mod p\).
      -- \(d\) must be {0, 1} as addition can only overflow so much.
      d :: Bool c
      nm :: FieldElement c
      um :: UIntFFA p r c
      (d, nm, um) = restore $ const
        ( fromCircuitF (arithmetize (nx, ux, ny, uy) Proxy)
            \((Par1 ni :*: ui) :*: (Par1 nj :*: uj)) -> do
              let add = valueFFA @p @r @c ni ui + valueFFA @p @r @c nj uj
              traverse unconstrained
                  $ Par1 (fromIntegral (add `div` p))
                  :*: layoutFFA @p @r @c (add `mod` p)
        , U1 :*: (U1 :*: U1))
      -- | Constraints:
      -- * boolean is indeed boolean;
      -- * UInt registers are indeed registers;
      -- * m < p;
      -- * equation holds modulo basefield;
      -- * equation holds modulo 2^k.
      Bool ck = isValid (d, FFA @p nm um)
                && (nx + ny == bool zero p d + nm)
                && (ux + uy == bool zero p d + um)
      -- | Sew constraints into result.
      (nr, ur) = restore $ const
        ( fromCircuitF (arithmetize (nm, um, ck) Proxy)
            \(ni :*: ui :*: Par1 b) -> do
              constraint (($ b) - one)
              return (ni :*: ui)
        , U1 :*: U1)

instance (Symbolic c, KnownFFA p r c, Scale a (Zp p)) => Scale a (FFA p r c) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Symbolic c, KnownFFA p r c) => AdditiveMonoid (FFA p r c) where
  zero = fromConstant (zero :: Zp p)

instance (Symbolic c, KnownFFA p r c) => AdditiveGroup (FFA p r c) where
  -- | negate cannot overflow if value is nonzero.
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
      pos = Prelude.fromIntegral (a `mod` Prelude.fromIntegral (value @p -! 1))
      neg = value @p -! (pos + 1)

instance (Symbolic c, KnownFFA p r c, Prime p) => Field (FFA p r c) where
  finv = Prelude.error "TODO"

instance Finite (Zp p) => Finite (FFA p r b) where
  type Order (FFA p r b) = p
