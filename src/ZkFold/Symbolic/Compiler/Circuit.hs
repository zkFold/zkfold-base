{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators         #-}

module ZkFold.Symbolic.Compiler.Circuit where

import           Control.Applicative
import           Control.Category
import           Data.Foldable
import           Data.Function                                (($))
import           Data.Functor
import           Data.Map.Strict                              (Map)
import qualified Data.Map.Strict                              as Map
import           Data.Monoid
import           Data.Semigroup
import           Data.Sequence                                (Seq)
import qualified Data.Sequence                                as Seq
import           Data.Traversable
import           Data.Type.Equality
import           GHC.Generics
import           Numeric.Natural                              (Natural)
import           Prelude                                      (Integer)
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Poly, var)

-- The input variables are numbered in decreasing order n..1
-- which is maintained as an invariant of the circuit.
data Circuit i o a = Circuit
  { systemC  :: Seq (Poly a Integer Natural)
    -- ^ The system of polynomial constraints,
    -- each polynomial constitutes a "multi-edge"
    -- of the circuit graph.
  , witnessC :: Map Integer (i a -> a)
    -- ^ The witness generation function
  , outputC  :: o Integer
    -- ^ The output variables
  }

instance o ~ U1 => Semigroup (Circuit i o a) where
  c1 <> c2 = Circuit
    { systemC = systemC c1 <> systemC c2
    , witnessC = witnessC c1 <> witnessC c2
    , outputC = U1
    }

instance (o ~ U1, Traversable i, VectorSpace a i) => Monoid (Circuit i o a) where
  mempty = Circuit mempty inputMap U1 where
    n = Prelude.fromIntegral (dimV @a @i)
    inserter m k = Map.insert k (\i -> toList i Prelude.!! Prelude.fromIntegral (k-1)) m
    inputMap = Prelude.foldl inserter Map.empty [1 .. n]

dimapC
  :: (i1 a -> i0 a)
  -> (o0 Integer -> o1 Integer)
  -> Circuit i0 o0 a -> Circuit i1 o1 a
dimapC f g c = c
  { witnessC = fmap (. f) (witnessC c)
  , outputC = g (outputC c)
  }

joinC :: Circuit i oL a -> Circuit i oR a -> Circuit i (oL :*: oR) a
joinC c1 c2 =
  (c1 {outputC = U1} <> c2 {outputC = U1})
    {outputC = outputC c1 :*: outputC c2}

concatC
  :: (Functor v, Foldable v, Traversable i, VectorSpace a i)
  => v (Circuit i o a) -> Circuit i (v :.: o) a
concatC cs =
  (foldMap (\c -> c {outputC = U1}) cs)
    {outputC = Comp1 (fmap outputC cs)}

evalC
  :: forall i o a. Functor o
  => Circuit i o a -> i a -> o a
evalC c i = fmap (\v -> (witnessC c Map.! v) i) (outputC c)

applyC :: i a -> Circuit (i :*: j) o a -> Circuit j o a
applyC i c = c {witnessC = fmap (. ((:*:) i)) (witnessC c) }

inputC :: forall a i. (VectorSpace a i, Traversable i) => i Integer
inputC = iterateV @a @i Prelude.pred (Prelude.fromIntegral (dimV @a @i))

idC :: forall a i. (VectorSpace a i, Traversable i) => Circuit i i a
idC = mempty {outputC = inputC @a}

class (forall i j. Functor (m i j))
  => MonadCircuit a m | m -> a where
    return :: x -> m i i x
    (>>=) :: m i j x -> (x -> m j k y) -> m i k y
    (>>) :: m i j x -> m j k y -> m i k y
    x >> y = x >>= \_ -> y
    (<¢>) :: m i j (x -> y) -> m j k x -> m i k y
    f <¢> x = f >>= (<$> x)
    apply :: i a -> m (i :*: j) j ()
    input :: (VectorSpace a i, Traversable i) => m i i (i Integer)
    input = return (inputC @a)
    newInput ::
      ( VectorSpace a i, Traversable i
      , VectorSpace a j, Traversable j
      ) => m j (i :*: j) (i Integer)
    eval :: (Traversable i, VectorSpace a i, Functor o) => m i i (o Integer) -> i a -> o a
    runCircuit :: Circuit i o a -> m i i (o Integer)
    constraint :: ClosedPoly Integer a -> m i i ()
    newConstrained :: NewConstraint Integer a -> ((Integer -> a) -> a) -> m i i Integer

type ClosedPoly i a = forall x . Algebra a x => (i -> x) -> x

type NewConstraint i a = forall x . Algebra a x => (i -> x) -> i -> x

circuit
  :: (Traversable i, VectorSpace a i, Field a, Prelude.Eq a)
  => (forall m. MonadCircuit a m => m i i (o Integer))
  -> Circuit i o a
circuit x =
  case runBlueprint x mempty of (o, c) -> c {outputC = o}

newtype Blueprint a i j x = Blueprint
  {runBlueprint :: Circuit i U1 a -> (x, Circuit j U1 a)}
  deriving Functor

instance (Field a, Prelude.Eq a) => Applicative (Blueprint a i i) where
  pure = return
  (<*>) = (<¢>)

instance (Field a, Prelude.Eq a) => MonadCircuit a (Blueprint a) where
  return x = Blueprint $ \c -> (x,c)
  m >>= f = Blueprint $ \c ->
    let
      (x, c') = runBlueprint m c
    in
      runBlueprint (f x) c'
  apply i = Blueprint $ \c -> ((), applyC i c)
  newInput = input >>= \i ->
    let
      iLen = Prelude.fromIntegral (length i)
    in
      Blueprint $ \c ->
        ( fmap (iLen +) (inputC @a)
        , dimapC (\(_ :*: j) -> j) id c
        )
  eval x i = case runBlueprint x mempty of
    (o, c) -> evalC (c {outputC = o}) i
  runCircuit c = Blueprint $ \c' ->
    (outputC c, c {outputC = U1} <> c')
  constraint p = Blueprint $ \c ->
    ((), c { systemC = p var Seq.<| systemC c })
  newConstrained p w = Blueprint $ \c ->
    let index = maximum (Map.keysSet $ witnessC c) + 1
     in (index, c { systemC = p var index Seq.<| systemC c
                  , witnessC = Map.insert index (\i -> w ((($ i) <$> witnessC c) Map.!)) $ witnessC c })
