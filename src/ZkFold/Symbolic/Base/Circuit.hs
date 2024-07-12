{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module ZkFold.Symbolic.Base.Circuit
  ( Circuit (..)
  , SysVar (..)
  , OutVar (..)
  , MonadCircuit (..)
  , evalC
  , idC
  , applyC
  ) where

import           Control.Applicative
import           Control.Category
import           Data.Either
import           Data.Eq
import           Data.Function                   (($))
import           Data.Functor
import           Data.IntMap                     (IntMap)
import qualified Data.IntMap                     as IntMap
import           Data.Maybe
import           Data.Monoid
import           Data.Ord
import           Data.Semigroup
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Data.Type.Equality

import           ZkFold.Symbolic.Base.Num
import           ZkFold.Symbolic.Base.Polynomial
import           ZkFold.Symbolic.Base.Vector

data Circuit x i o = Circuit
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
  , outputC  :: o (OutVar x i)
    -- ^ The output variables,
    -- they can be input, constant or new variables.
  }

data SysVar x i
  = InVar (Basis x i)
  | NewVar Int
deriving stock instance VectorSpace x i => Eq (SysVar x i)
deriving stock instance VectorSpace x i => Ord (SysVar x i)

data OutVar x i
  = SysVar (SysVar x i)
  | ConstVar x
deriving stock instance (Eq x, VectorSpace x i) => Eq (OutVar x i)
deriving stock instance (Ord x, VectorSpace x i) => Ord (OutVar x i)

witnessIndex
  :: VectorSpace x i
  => i x -> IntMap (i x -> x) -> OutVar x i -> x
witnessIndex inp witnessMap = \case
  SysVar (InVar basisIx) -> indexV inp basisIx
  SysVar (NewVar ix) -> fromMaybe zero (($ inp) <$> witnessMap IntMap.!? ix)
  ConstVar x -> x

instance (Ord x, VectorSpace x i, o ~ U1) => Monoid (Circuit x i o) where
  mempty = Circuit mempty mempty U1
instance (Ord x, VectorSpace x i, o ~ U1) => Semigroup (Circuit x i o) where
  c0 <> c1 = Circuit
    { systemC = systemC c0 <> systemC c1
    , witnessC = witnessC c0 <> witnessC c1
    , outputC = U1
    }

evalC :: (VectorSpace x i, Functor o) => Circuit x i o -> i x -> o x
evalC c i = fmap (witnessIndex i (witnessC c)) (outputC c)

applyC
  :: (Ord x, Algebra x x, VectorSpace x i, VectorSpace x j, Functor o)
  => i x -> Circuit x (i :*: j) o -> Circuit x j o
applyC i c = c
  { systemC = Set.map (mapPoly sysF) (systemC c)
  , witnessC = fmap witF (witnessC c)
  , outputC = fmap outF (outputC c)
  } where
      sysF = \case
        InVar (Left bi) -> Left (indexV i bi)
        InVar (Right bj) -> Right (InVar bj)
        NewVar n -> Right (NewVar n)
      witF f j = f (i :*: j)
      outF = \case
        SysVar (InVar (Left bi)) -> ConstVar (indexV i bi)
        SysVar (InVar (Right bj)) -> SysVar (InVar bj)
        SysVar (NewVar n) -> SysVar (NewVar n)
        ConstVar x -> ConstVar x

newInputC
  :: (Ord x, Algebra x x, VectorSpace x i, VectorSpace x j, Functor o)
  => Circuit x j o -> Circuit x (i :*: j) o
newInputC c = c
  { systemC = Set.map (mapPoly sysF) (systemC c)
  , witnessC = fmap witF (witnessC c)
  , outputC = fmap outF (outputC c)
  } where
    sysF = \case
      InVar bj -> Right (InVar (Right bj))
      NewVar n -> Right (NewVar n)
    witF f (_ :*: j) = f j
    outF = \case
      SysVar (InVar bj) -> SysVar (InVar (Right bj))
      SysVar (NewVar n) -> SysVar (NewVar n)
      ConstVar k -> ConstVar k

inputC :: forall x i. VectorSpace x i => i (OutVar x i)
inputC = fmap (SysVar . InVar) (basisV @x)

idC :: forall x i. (Ord x, VectorSpace x i) => Circuit x i i
idC = mempty {outputC = inputC}

class (forall i j. Functor (m i j))
  => MonadCircuit x m | m -> x where
    apply :: (VectorSpace x i, VectorSpace x j) => i x -> m (i :*: j) j ()
    newInput :: (VectorSpace x i, VectorSpace x j) => m j (i :*: j) ()
    return :: r -> m i i r
    (>>=) :: m i j r -> (r -> m j k s) -> m i k s
    (>>) :: m i j r -> m j k s -> m i k s
    x >> y = x >>= \_ -> y
    (<¢>) :: m i j (r -> s) -> m j k r -> m i k s
    f <¢> x = f >>= (<$> x)
    input :: VectorSpace x i => m i i (i (OutVar x i))
    input = return (inputC @x)
    eval :: (VectorSpace x i, Functor o) => m i i (o (OutVar x i)) -> i x -> o x
    runCircuit :: VectorSpace x i => Circuit x i o -> m i i (o (OutVar x i))
    constraint
      :: VectorSpace x i
      => (forall a. Algebra x a => (SysVar x i -> a) -> a)
      -> m i i ()
    newConstrained
      :: VectorSpace x i
      => (forall a. Algebra x a => (Int -> a) -> Int -> a)
      -> ((Int -> x) -> x)
      -> m i i (OutVar x i)

newtype Blueprint x i j r = Blueprint
  {runBlueprint :: Circuit x i U1 -> (r, Circuit x j U1)}
  deriving Functor

instance (Algebra x x, Ord x) => Applicative (Blueprint x i i) where
  pure = return
  (<*>) = (<¢>)

instance (Algebra x x, Ord x) => MonadCircuit x (Blueprint x) where
  return x = Blueprint $ \c -> (x,c)
  m >>= f = Blueprint $ \c ->
    let
      (x, c') = runBlueprint m c
    in
      runBlueprint (f x) c'
  apply i = Blueprint $ \c -> ((), applyC i c)
  newInput = Blueprint $ \c -> ((), newInputC c)
  eval x i = case runBlueprint x mempty of
    (o, c) -> evalC (c {outputC = o}) i
  runCircuit c = Blueprint $ \c' ->
    (outputC c, c {outputC = U1} <> c')
  constraint p = Blueprint $ \c ->
    ((), c { systemC = Set.insert (p var) (systemC c) })
  newConstrained p w = Blueprint $ \c ->
    let
      (maxIndex, _) = IntMap.findMax (witnessC c)
      newIndex = maxIndex + 1
      newWitness i = w (fromMaybe zero . ((($ i) <$> witnessC c) IntMap.!?))
     in
      ( SysVar (NewVar newIndex)
      , c { systemC = Set.insert (p (var . NewVar) newIndex) (systemC c)
          , witnessC = IntMap.insert newIndex newWitness (witnessC c)
          }
      )
