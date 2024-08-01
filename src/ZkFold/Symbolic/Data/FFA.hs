{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FFA where

import           Control.Monad                                             (return, (>>=))
import           Data.Foldable                                             (any, foldlM)
import           Data.Function                                             (const, ($), (.))
import           Data.Functor                                              (fmap, (<$>))
import           Data.List                                                 (dropWhile, (++))
import           Data.Ratio                                                ((%))
import           Data.Traversable                                          (for, traverse)
import           Data.Tuple                                                (fst, snd, uncurry)
import           Data.Zip                                                  (zipWith)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   (Integer, error)
import qualified Prelude                                                   as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, inv)
import           ZkFold.Base.Algebra.Basic.Number                          (KnownNat, value)
import           ZkFold.Base.Data.Vector
import           ZkFold.Prelude                                            (iterateM, length)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, splitExpansion)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint, circuitF, runCircuit)
import           ZkFold.Symbolic.Data.Combinators                          (log2, maxBitsPerFieldElement)
import           ZkFold.Symbolic.Data.Ord                                  (blueprintGE)
import           ZkFold.Symbolic.Interpreter
import           ZkFold.Symbolic.MonadCircuit                              (newAssigned)

type Size = 7

-- | Foreign-field arithmetic based on https://cr.yp.to/papers/mmecrt.pdf
newtype FFA (p :: Natural) b = FFA (b (Vector Size))

deriving newtype instance Arithmetic a => SymbolicData a (FFA p (ArithmeticCircuit a))

coprimesDownFrom :: KnownNat n => Natural -> Vector n Natural
coprimesDownFrom n = unfold (uncurry step) ([], [n,n-!1..0])
  where
    step ans xs =
      case dropWhile (\x -> any ((Haskell./= 1) . Haskell.gcd x) ans) xs of
        []      -> error "no options left"
        (x:xs') -> (x, (ans ++ [x], xs'))

coprimes :: forall a. Finite a => Vector Size Natural
coprimes = coprimesDownFrom @Size $ 2 ^ (maxBitsPerFieldElement @a `div` 2)

sigma :: Natural
sigma = Haskell.ceiling (log2 $ value @Size) + 1 :: Natural

mprod0 :: forall a. Finite a => Natural
mprod0 = product (coprimes @a)

mprod :: forall a p . (Finite a, KnownNat p) => Natural
mprod = mprod0 @a `mod` value @p

mis0 :: forall a. Finite a => Vector Size Natural
mis0 = let (c, m) = (coprimes @a, mprod0 @a) in (m `div`) <$> c

mis :: forall a p. (Finite a, KnownNat p) => Vector Size Natural
mis = (`mod` value @p) <$> mis0 @a

minv :: forall a. Finite a => Vector Size Natural
minv = zipWith (\x p -> fromConstant x `inv` p) (mis0 @a) (coprimes @a)

instance (KnownNat p, Finite (Zp q), ToConstant (Zp p) c) => ToConstant (FFA p (Interpreter (Zp q))) c where
  toConstant = (toConstant :: Zp p -> c) . fromConstant . impl
    where
      mods = coprimes @(Zp q)
      binary g m = (fromConstant g * 2 ^ sigma) `div` fromConstant m
      impl (FFA (Interpreter xs)) =
        let gs0 = zipWith (\x y -> toConstant x * y) xs $ minv @(Zp q)
            gs = zipWith mod gs0 mods
            residue = floorN ((3 % 4) + sum (zipWith binary gs mods) % (2 ^ sigma))
         in vectorDotProduct gs (mis @(Zp q) @p) -! mprod @(Zp q) @p * residue

instance (FromConstant c (Zp p), Finite (Zp q)) => FromConstant c (FFA p (Interpreter (Zp q))) where
  fromConstant = FFA . Interpreter . impl . toConstant . (fromConstant :: c -> Zp p)
    where
      impl :: Natural -> Vector Size (Zp q)
      impl x = fromConstant . (x `mod`) <$> coprimes @(Zp q)

instance (FromConstant c (Zp p), Arithmetic a) => FromConstant c (FFA p (ArithmeticCircuit a)) where
  fromConstant = FFA . impl . toConstant . (fromConstant :: c -> Zp p)
    where
      impl :: Natural -> ArithmeticCircuit a (Vector Size)
      impl x = circuitF $ for (coprimes @a) $ \m -> newAssigned (fromConstant (x `mod` m))

condSubOF :: forall i a m . MonadBlueprint i a m => Natural -> i -> m (i, i)
condSubOF m i = do
  z <- newAssigned zero
  o <- newAssigned one
  let bm = (\x -> if x Haskell.== 0 then z else o) <$> (binaryExpansion m ++ [0])
  bi <- expansion (length bm) i
  ovf <- blueprintGE (Haskell.reverse bi) (Haskell.reverse bm)
  res <- newAssigned (($ i) - ($ ovf) * fromConstant m)
  return (res, ovf)

condSub :: MonadBlueprint i a m => Natural -> i -> m i
condSub m x = fst <$> condSubOF m x

smallCut :: forall i a m. (Arithmetic a, MonadBlueprint i a m) => Vector Size i -> m (Vector Size i)
smallCut = zipWithM condSub $ coprimes @a

bigSub :: MonadBlueprint i a m => Natural -> i -> m i
bigSub m j = trimPow j >>= trimPow >>= condSub m
  where
    s = Haskell.ceiling (log2 m) :: Natural
    trimPow i = do
      (l, h) <- splitExpansion s s i
      newAssigned (($ l) + ($ h) * fromConstant ((2 ^ s) -! m))

bigCut :: forall i a m. (Arithmetic a, MonadBlueprint i a m) => Vector Size i -> m (Vector Size i)
bigCut = zipWithM bigSub $ coprimes @a

cast :: forall p i a m. (KnownNat p, Arithmetic a, MonadBlueprint i a m) => Vector Size i -> m (Vector Size i)
cast xs = do
  gs <- zipWithM (\i m -> newAssigned $ ($ i) * fromConstant m) xs (minv @a) >>= bigCut
  zi <- newAssigned (const zero)
  let binary g m = snd <$> iterateM sigma (binstep m) (g, zi)
      binstep m (i, ci) = do
        (i', j) <- newAssigned (($ i) + ($ i)) >>= condSubOF @i @a @m m
        ci' <- newAssigned (($ ci) + ($ ci) + ($ j))
        return (i', ci')
  base <- newAssigned (fromConstant (3 * (2 ^ (sigma -! 2)) :: Natural))
  let ms = coprimes @a
  residue <- zipWithM binary gs ms
        >>= foldlM (\i j -> newAssigned (($ i) + ($ j))) base
        >>= (fmap snd . splitExpansion sigma (numberOfBits @a -! sigma))
  for ms $ \m -> do
    dot <- zipWithM (\i x -> newAssigned (($ i) * fromConstant (x `mod` m))) gs (mis @a @p)
            >>= traverse (bigSub m)
            >>= foldlM (\i j -> newAssigned (($ i) + ($ j))) zi
    newAssigned (($ dot) + fromConstant (m -! (mprod @a @p `mod` m)) * ($ residue))
        >>= bigSub m

instance (Finite (Zp p), Finite (Zp q)) => MultiplicativeSemigroup (FFA p (Interpreter (Zp q))) where
  x * y = fromConstant (toConstant x * toConstant y :: Zp p)

instance (KnownNat p, Arithmetic a) => MultiplicativeSemigroup (FFA p (ArithmeticCircuit a)) where
  FFA q * FFA r = FFA $ circuitF $ do
    xs <- runCircuit q
    ys <- runCircuit r
    zs <- zipWithM (\i j -> newAssigned (($ i) * ($ j))) xs ys
    bigCut zs >>= cast @p

instance (Finite (Zp p), Finite (Zp q)) => Exponent (FFA p (Interpreter (Zp q))) Natural where
  x ^ a = fromConstant (toConstant x ^ a :: Zp p)

instance (Finite (Zp p), Arithmetic a) => Exponent (FFA p (ArithmeticCircuit a)) Natural where
  (^) = natPow

instance (Finite (Zp p), Finite (Zp q)) => MultiplicativeMonoid (FFA p (Interpreter (Zp q))) where
  one = fromConstant (one :: Zp p)

instance (Finite (Zp p), Arithmetic a) => MultiplicativeMonoid (FFA p (ArithmeticCircuit a)) where
  one = fromConstant (one :: Zp p)

instance (Finite (Zp p), Finite (Zp q)) => AdditiveSemigroup (FFA p (Interpreter (Zp q))) where
  x + y = fromConstant (toConstant x + toConstant y :: Zp p)

instance (KnownNat p, Arithmetic a) => AdditiveSemigroup (FFA p (ArithmeticCircuit a)) where
  FFA q + FFA r = FFA $ circuitF $ do
    xs <- runCircuit q
    ys <- runCircuit r
    zs <- zipWithM (\i j -> newAssigned (($ i) + ($ j))) xs ys
    smallCut zs >>= cast @p

instance (Finite (Zp p), Scale c (Zp p), Finite (Zp q)) => Scale c (FFA p (Interpreter (Zp q))) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Finite (Zp p), Scale c (Zp p), Arithmetic a) => Scale c (FFA p (ArithmeticCircuit a)) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (Finite (Zp p), FromConstant (Zp p) (FFA p b), Scale Natural (FFA p b), AdditiveSemigroup (FFA p b)) => AdditiveMonoid (FFA p b) where
  zero = fromConstant (zero :: Zp p)

instance (Finite (Zp p), Finite (Zp q)) => AdditiveGroup (FFA p (Interpreter (Zp q))) where
  negate = fromConstant . negate @(Zp p) . toConstant

instance (Finite (Zp p), Arithmetic a) => AdditiveGroup (FFA p (ArithmeticCircuit a)) where
  negate (FFA r) = FFA $ circuitF $ do
    xs <- runCircuit r
    ys <- zipWithM (\i m -> newAssigned $ fromConstant m - ($ i)) xs $ coprimes @a
    cast @p ys

instance (MultiplicativeMonoid (FFA p b), AdditiveMonoid (FFA p b), FromConstant Natural (FFA p b)) => Semiring (FFA p b)

instance (Semiring (FFA p b), AdditiveGroup (FFA p b), FromConstant Integer (FFA p b)) => Ring (FFA p b)

instance (PrimeField (Zp p), Finite (Zp q)) => Exponent (FFA p (Interpreter (Zp q))) Integer where
  x ^ a = fromConstant (toConstant x ^ a :: Zp p)

instance (PrimeField (Zp p), Arithmetic a) => Exponent (FFA p (ArithmeticCircuit a)) Integer where
  x ^ a = x `intPowF` (a `mod` fromConstant (value @p -! 1))

instance (PrimeField (Zp p), Finite (Zp q)) => Field (FFA p (Interpreter (Zp q))) where
  finv = fromConstant . finv @(Zp p) . toConstant

instance (PrimeField (Zp p), Arithmetic a) => Field (FFA p (ArithmeticCircuit a)) where
  finv x = x ^ (value @p -! 2)

instance Finite (Zp p) => Finite (FFA p b) where
  type Order (FFA p b) = p
