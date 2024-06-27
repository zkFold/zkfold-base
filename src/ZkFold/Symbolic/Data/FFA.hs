{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances  #-}

module ZkFold.Symbolic.Data.FFA where

import           Control.Monad                                             (return)
import           Data.Function                                             (($), (.))
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   (Integer, error)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Base.Algebra.Basic.Number                          (KnownNat, value)
import           ZkFold.Base.Data.Vector                                   (Vector (..), zipWithM)
import           ZkFold.Symbolic.Compiler                                  (Arithmetic, ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (circuitN, newAssigned, runCircuit)
import           ZkFold.Symbolic.Data.Combinators                          (maxBitsPerFieldElement)

newtype FFA (p :: Natural) b a = FFA (b 3 a)

coprimes :: forall a. Finite a => (Natural, Natural, Natural)
coprimes = let n = 2 ^ (maxBitsPerFieldElement @a `div` 2) in (n, n -! 1, n -! 3)

instance (KnownNat p, ToConstant (Zp p) c) => ToConstant (FFA p Vector (Zp q)) c where
  toConstant = (toConstant :: Zp p -> c) . fromConstant . impl
    where
      impl :: FFA p Vector (Zp q) -> Natural
      impl = error "TODO"

instance (FromConstant c (Zp p), Finite (Zp q)) => FromConstant c (FFA p Vector (Zp q)) where
  fromConstant = impl . toConstant . (fromConstant :: c -> Zp p)
    where
      (a, b, c) = coprimes @(Zp q)
      impl :: Natural -> FFA p Vector (Zp q)
      impl x = FFA $ Vector [
        fromConstant (x `mod` a),
        fromConstant (x `mod` b),
        fromConstant (x `mod` c)
        ]

instance (FromConstant c (Zp p), Arithmetic a) => FromConstant c (FFA p ArithmeticCircuit a) where
  fromConstant = impl . toConstant . (fromConstant :: c -> Zp p)
    where
      (a, b, c) = coprimes @a
      impl :: Natural -> FFA p ArithmeticCircuit a
      impl x = FFA $ circuitN $ do
        i <- newAssigned (\_ -> fromConstant (x `mod` a))
        j <- newAssigned (\_ -> fromConstant (x `mod` b))
        k <- newAssigned (\_ -> fromConstant (x `mod` c))
        return $ Vector [i, j, k]

cast :: Vector 3 i -> m (Vector 3 i)
cast = error "TODO"

instance (Finite (Zp p), Finite (Zp q)) => MultiplicativeSemigroup (FFA p Vector (Zp q)) where
  x * y = fromConstant (toConstant x * toConstant y :: Zp p)

instance Arithmetic a => MultiplicativeSemigroup (FFA p ArithmeticCircuit a) where
  FFA q * FFA r = FFA $ circuitN $ do
    xs <- runCircuit q
    ys <- runCircuit r
    zs <- zipWithM (\i j -> newAssigned (($ i) * ($ j))) xs ys
    cast zs

instance (Finite (Zp p), Finite (Zp q)) => Exponent (FFA p Vector (Zp q)) Natural where
  x ^ a = fromConstant (toConstant x ^ a :: Zp p)

instance (Finite (Zp p), Arithmetic a) => Exponent (FFA p ArithmeticCircuit a) Natural where
  (^) = natPow

instance (Finite (Zp p), Finite (Zp q)) => MultiplicativeMonoid (FFA p Vector (Zp q)) where
  one = fromConstant (one :: Zp p)

instance (Finite (Zp p), Arithmetic a) => MultiplicativeMonoid (FFA p ArithmeticCircuit a) where
  one = fromConstant (one :: Zp p)

instance (Finite (Zp p), Finite (Zp q)) => AdditiveSemigroup (FFA p Vector (Zp q)) where
  x + y = fromConstant (toConstant x + toConstant y :: Zp p)

instance Arithmetic a => AdditiveSemigroup (FFA p ArithmeticCircuit a) where
  FFA q + FFA r = FFA $ circuitN $ do
    xs <- runCircuit q
    ys <- runCircuit r
    zs <- zipWithM (\i j -> newAssigned (($ i) + ($ j))) xs ys
    cast zs

instance (Finite (Zp p), Scale c (Zp p), Finite (Zp q)) => Scale c (FFA p Vector (Zp q)) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Finite (Zp p), Scale c (Zp p), Arithmetic a) => Scale c (FFA p ArithmeticCircuit a) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Finite (Zp p), FromConstant (Zp p) (FFA p b a), Scale Natural (FFA p b a), AdditiveSemigroup (FFA p b a)) => AdditiveMonoid (FFA p b a) where
  zero = fromConstant (zero :: Zp p)

instance (Finite (Zp p), Finite (Zp q)) => AdditiveGroup (FFA p Vector (Zp q)) where
  negate = fromConstant . negate @(Zp p) . toConstant

instance (Finite (Zp p), Arithmetic a) => AdditiveGroup (FFA p ArithmeticCircuit a) where
  negate (FFA q) = FFA $ circuitN $ do
    Vector xs <- runCircuit q
    let (x, y, z) = case xs of { [u, v, w] -> (u, v, w); _ -> error "negate: impossible" }
        (a, b, c) = coprimes @a
    i <- newAssigned (\w -> fromConstant a - w x)
    j <- newAssigned (\w -> fromConstant b - w y)
    k <- newAssigned (\w -> fromConstant c - w z)
    cast $ Vector [i, j, k]

instance (MultiplicativeMonoid (FFA p b a), AdditiveMonoid (FFA p b a), FromConstant Natural (FFA p b a)) => Semiring (FFA p b a)

instance (Semiring (FFA p b a), AdditiveGroup (FFA p b a), FromConstant Integer (FFA p b a)) => Ring (FFA p b a)

instance (PrimeField (Zp p), Finite (Zp q)) => Exponent (FFA p Vector (Zp q)) Integer where
  x ^ a = fromConstant (toConstant x ^ a :: Zp p)

instance (PrimeField (Zp p), Arithmetic a) => Exponent (FFA p ArithmeticCircuit a) Integer where
  x ^ a = x `intPowF` (a `mod` fromConstant (value @p -! 1))

instance (PrimeField (Zp p), Finite (Zp q)) => Field (FFA p Vector (Zp q)) where
  finv = fromConstant . finv @(Zp p) . toConstant

instance (PrimeField (Zp p), Arithmetic a) => Field (FFA p ArithmeticCircuit a) where
  finv x = x ^ (value @p -! 2)

instance Finite (Zp p) => Finite (FFA p b a) where
  type Order (FFA p b a) = p
