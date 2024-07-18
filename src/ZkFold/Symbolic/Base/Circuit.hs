{-# LANGUAGE
AllowAmbiguousTypes
, DerivingStrategies
, DerivingVia
, QuantifiedConstraints
, RankNTypes
, TypeOperators
, UndecidableInstances
, UndecidableSuperClasses
#-}

module ZkFold.Symbolic.Base.Circuit
  ( Circuit (..), circuit, evalC
  , MonadCircuit (..)
  , IxMonadCircuit (..)
  , CircuitIx (..)
  , Blueprint
  , SysVar (..)
  , Var (..)
  , Register (..)
  , binaryExpansion
  ) where

import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Indexed
import Data.Either
import Data.Eq
import Data.Foldable hiding (sum, product)
import Data.Function (($))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Data.Type.Equality
import qualified Data.Vector as V
import qualified Prelude

import           ZkFold.Symbolic.Base.Num
import           ZkFold.Symbolic.Base.Polynomial
import           ZkFold.Symbolic.Base.Vector

data Circuit x i o = UnsafeCircuit
  { systemC  :: Set (Poly (SysVar x i) Natural x)
    -- ^ The system of polynomial constraints,
    -- each polynomial constitutes a "multi-edge" of the circuit graph,
    -- whose "vertices" are variables.
    -- Polynomials constrain input variables and new variables.
    -- Constant variables are absorbed into the polynomial coefficients.
  , witnessC :: IntMap (i x -> x)
    -- ^ The witness generation map,
    -- witness functions for new variables.
    -- Input and constant variables don't need witness functions.
  , outputC  :: o (Var x i)
    -- ^ The output variables,
    -- they can be input, constant or new variables.
  }

type Blueprint x i o =
  forall t m. (IxMonadCircuit x t, Monad m) => t i i m (o (Var x i))

circuit
  :: (Ord x, VectorSpace x i)
  => Blueprint x i o
  -> Circuit x i o
circuit m = case unPar1 (runCircuitIx m mempty) of
  (o, c) -> c {outputC = o}

evalC :: (VectorSpace x i, Functor o) => Circuit x i o -> i x -> o x
evalC c i = fmap (indexW (witnessC c) i) (outputC c)

data SysVar x i
  = InVar (Basis x i)
  | NewVar Int
deriving stock instance VectorSpace x i => Eq (SysVar x i)
deriving stock instance VectorSpace x i => Ord (SysVar x i)

data Var x i
  = SysVar (SysVar x i)
  | ConstVar x
deriving stock instance (Eq x, VectorSpace x i) => Eq (Var x i)
deriving stock instance (Ord x, VectorSpace x i) => Ord (Var x i)

evalConst
  :: (Ord x, VectorSpace x i)
  => Poly (Var x i) Natural x
  -> Poly (SysVar x i) Natural x
evalConst = mapPoly $ \case
  ConstVar x -> Left x
  SysVar v -> Right v

indexW
  :: VectorSpace x i
  => IntMap (i x -> x) -> i x -> Var x i -> x
indexW witnessMap inp = \case
  SysVar (InVar basisIx) -> indexV inp basisIx
  SysVar (NewVar ix) -> fromMaybe zero (($ inp) <$> witnessMap IntMap.!? ix)
  ConstVar x -> x

instance (Ord x, VectorSpace x i, o ~ U1) => Monoid (Circuit x i o) where
  mempty = UnsafeCircuit mempty mempty U1
instance (Ord x, VectorSpace x i, o ~ U1) => Semigroup (Circuit x i o) where
  c0 <> c1 = UnsafeCircuit
    { systemC = systemC c0 <> systemC c1
    , witnessC = witnessC c0 <> witnessC c1
    , outputC = U1
    }

class Monad m => MonadCircuit x i m | m -> x, m -> i where
  runCircuit
    :: VectorSpace x i
    => Circuit x i o -> m (o (Var x i))
  input :: VectorSpace x i => m (i (Var x i))
  input = return (fmap (SysVar . InVar) (basisV @x))
  constraint
    :: VectorSpace x i
    => (forall a. Algebra x a => (Var x i -> a) -> a)
    -> m ()
  newConstrained
    :: VectorSpace x i
    => (forall a. Algebra x a => (Var x i -> a) -> Var x i -> a)
    -> ((Var x i -> x) -> x)
    -> m (Var x i)
  newAssigned
    :: VectorSpace x i
    => (forall a. Algebra x a => (Var x i -> a) -> a)
    -> m (Var x i)
  newAssigned p = newConstrained (\x i -> p x - x i) p

class
  ( forall i m. Monad m => MonadCircuit x i (t i i m)
  , IxMonadTrans t
  ) => IxMonadCircuit x t | t -> x where
    apply
      :: (VectorSpace x i, VectorSpace x j, Monad m)
      => i x -> t (i :*: j) j m ()
    newInput
      :: (VectorSpace x i, VectorSpace x j, Monad m)
      => t j (i :*: j) m ()

newtype CircuitIx x i j m r = UnsafeCircuitIx
  {runCircuitIx :: Circuit x i U1 -> m (r, Circuit x j U1)}
  deriving Functor

instance (Field x, Ord x, Monad m)
  => Applicative (CircuitIx x i i m) where
    pure x = UnsafeCircuitIx $ \c -> return (x,c)
    (<*>) = apIx

instance (Field x, Ord x, Monad m)
  => Monad (CircuitIx x i i m) where
    return = pure
    (>>=) = Prelude.flip bindIx

instance (Field x, Ord x, Monad m)
  => MonadCircuit x i (CircuitIx x i i m) where

    runCircuit c = UnsafeCircuitIx $ \c' -> return
      (outputC c, c {outputC = U1} <> c')

    constraint p = UnsafeCircuitIx $ \c -> return
      ((), c {systemC = Set.insert (evalConst (p var)) (systemC c)})

    newConstrained p w = UnsafeCircuitIx $ \c -> return $
      let
        maxIndexMaybe = IntMap.lookupMax (witnessC c)
        newIndex = maybe 0 ((1 +) . Prelude.fst) maxIndexMaybe
        newWitness = w . indexW (witnessC c)
        outVar = SysVar (NewVar newIndex)
        newConstraint = evalConst (p var outVar)
        newSystemC = Set.insert newConstraint (systemC c)
        newWitnessC = IntMap.insert newIndex newWitness (witnessC c)
      in
        (outVar, c {systemC = newSystemC, witnessC = newWitnessC})

instance (i ~ j, Ord x, Field x)
  => MonadTrans (CircuitIx x i j) where
    lift m = UnsafeCircuitIx $ \c -> (, c) <$> m

instance (Field x, Ord x) => IxMonadTrans (CircuitIx x) where
  joinIx (UnsafeCircuitIx f) = UnsafeCircuitIx $ \c -> do
    (UnsafeCircuitIx g, c') <- f c
    g c'

instance (Field x, Ord x)
  => IxMonadCircuit x (CircuitIx x) where
    apply i = UnsafeCircuitIx $ \c -> return
      ( ()
      , c { systemC = Set.map (mapPoly sysF) (systemC c)
          , witnessC = fmap witF (witnessC c)
          , outputC = U1
          }
      ) where
          sysF = \case
            InVar (Left bi) -> Left (indexV i bi)
            InVar (Right bj) -> Right (InVar bj)
            NewVar n -> Right (NewVar n)
          witF f j = f (i :*: j)

    newInput = UnsafeCircuitIx $ \c -> return
      ( ()
      , c { systemC = Set.map (mapPoly sysF) (systemC c)
          , witnessC = fmap witF (witnessC c)
          , outputC = U1
          }
      )
      where
        sysF = \case
          InVar bj -> Right (InVar (Right bj))
          NewVar n -> Right (NewVar n)
        witF f (_ :*: j) = f j

instance (Ord x, VectorSpace x i)
  => From x (Circuit x i Par1) where
    from x = mempty { outputC = Par1 (ConstVar x) }

instance (Ord x, VectorSpace x i)
  => AdditiveMonoid (Circuit x i Par1) where
    zero = from @x zero
    c0 + c1 = circuit $ do
      Par1 v0 <- runCircuit c0
      Par1 v1 <- runCircuit c1
      Par1 <$> newAssigned (\x -> x v0 + x v1)

instance (Ord x, VectorSpace x i)
  => AdditiveGroup (Circuit x i Par1) where
    negate c = circuit $ do
      Par1 v <- runCircuit c
      Par1 <$> newAssigned (\x -> negate (x v))
    c0 - c1 = circuit $ do
      Par1 v0 <- runCircuit c0
      Par1 v1 <- runCircuit c1
      Par1 <$> newAssigned (\x -> x v0 - x v1)

instance (Ord x, VectorSpace x i)
  => From Natural (Circuit x i Par1) where
    from = from @x . from

instance (Ord x, VectorSpace x i)
  => From Integer (Circuit x i Par1) where
    from = from @x . from

instance (Ord x, VectorSpace x i)
  => From Rational (Circuit x i Par1) where
    from = from @x . from

instance (Ord x, VectorSpace x i)
  => MultiplicativeMonoid (Circuit x i Par1) where
    one = from @x one
    c0 * c1 = circuit $ do
      Par1 v0 <- runCircuit c0
      Par1 v1 <- runCircuit c1
      Par1 <$> newAssigned (\x -> x v0 * x v1)

instance From (Circuit x i Par1) (Circuit x i Par1)

instance (Ord x, VectorSpace x i)
  => Scalar Natural (Circuit x i Par1) where
    scale = scale @x . from
    combine = combineN

instance (Ord x, VectorSpace x i)
  => Scalar Integer (Circuit x i Par1) where
    scale = scale @x . from
    combine = combineZ

instance (Ord x, VectorSpace x i)
  => Scalar Rational (Circuit x i Par1) where
    scale = scale @x . from
    combine xs = sum [ scale k x | (k, x) <- xs ]

instance (Ord x, VectorSpace x i)
  => Scalar x (Circuit x i Par1) where
    scale k c = circuit $ do
      Par1 v <- runCircuit c
      Par1 <$> newAssigned (\x -> k `scale` x v)
    combine xs = sum [ scale k x | (k, x) <- xs ]

instance (Ord x, VectorSpace x i)
  => Scalar (Circuit x i Par1) (Circuit x i Par1)

instance (Ord x, VectorSpace x i)
  => Exponent Natural (Circuit x i Par1) where
    exponent x p = evalMono [(x, p)]
    evalMono = evalMonoN

instance (Ord x, Discrete x, VectorSpace x i)
  => MultiplicativeGroup (Circuit x i Par1) where
    recip c =
      let
        cInv = invertC c
        _ :*: inv = outputC cInv
      in
        cInv { outputC = inv }

instance (Ord x, Discrete x, VectorSpace x i)
  => Discrete (Circuit x i Par1) where
    dichotomy x y = isZero (x - y)
    isZero c =
      let
        cInv = invertC c
        isZ :*: _ = outputC cInv
      in
        cInv { outputC = isZ }

invertC
  :: (Ord x, Discrete x, VectorSpace x i)
  => Circuit x i Par1 -> Circuit x i (Par1 :*: Par1)
invertC c = circuit $ do
  Par1 v <- runCircuit c
  isZ <- newConstrained
    (\x i -> let xi = x i in xi * (xi - one))
    (\x -> isZero (x v))
  inv <- newConstrained
    (\x i -> x i * x v + x isZ - one)
    (\x -> recip (x v))
  return (Par1 isZ :*: Par1 inv)

-- A list of bits whose length is the number of bits
-- needed to represent an element of
-- the Arithmetic field of a Symbolic field extension.
newtype Register a = UnsafeRegister {fromRegister :: V.Vector a}
  deriving stock (Functor, Foldable, Traversable)
instance Symbolic a => VectorSpace a Register where
  type Basis a Register = Int
  indexV (UnsafeRegister v) ix = fromMaybe zero (v V.!? ix)
  dimV = numberOfBits @(Arithmetic a)
  basisV = UnsafeRegister (V.generate (from (dimV @a @Register)) id)
  tabulateV f = UnsafeRegister (V.generate (from (dimV @a @Register)) f)

binaryExpansion
  :: forall x i. (PrimeField x, VectorSpace x i)
  => Circuit x i Par1
  -> Circuit x i Register
binaryExpansion c = circuit $ do
  Par1 v <- runCircuit c
  lst <- expansion (from (numberOfBits @x)) v
  return (UnsafeRegister (V.fromList lst))

horner
  :: (VectorSpace x i, MonadCircuit x i m)
  => [Var x i] -> m (Var x i)
-- ^ @horner [b0,...,bn]@ computes the sum @b0 + 2 b1 + ... + 2^n bn@ using
-- Horner's scheme.
horner xs = case Prelude.reverse xs of
  []       -> return (ConstVar zero)
  (b : bs) ->
    foldlM (\a i -> newAssigned (\x -> let xa = x a in x i + xa + xa)) b bs

bitsOf
  :: (SemiEuclidean x, VectorSpace x i, MonadCircuit x i m)
  => Int -> Var x i -> m [Var x i]
-- ^ @bitsOf n k@ creates @n@ bits and
-- sets their witnesses equal to @n@ smaller bits of @k@.
bitsOf n k = for [0 .. n - 1] $ \j -> newConstrained
  (\x i -> let xi = x i in xi * (xi - one))
  ((Prelude.!! j) . expand . ($ k))
    where
      two = from (2 :: Natural)
      expand x = let (d,m) = divMod x two in m : expand d

expansion
  :: (SemiEuclidean x, VectorSpace x i, MonadCircuit x i m)
  => Int -> Var x i -> m [Var x i]
-- ^ @expansion n k@ computes a binary expansion of @k@ if it fits in @n@ bits.
expansion n k = do
    bits <- bitsOf n k
    k' <- horner bits
    constraint (\x -> x k - x k')
    return bits
