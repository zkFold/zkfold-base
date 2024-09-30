{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FFA (FFA (..)) where

import           Control.Applicative              (pure)
import           Control.Monad                    (Monad, return, (>>=))
import Control.DeepSeq (NFData)
import           Data.Foldable                    (any, foldlM)
import           Data.Function                    (const, ($), (.))
import           Data.Functor                     (fmap, (<$>))
import           Data.List                        (dropWhile, (++))
import           Data.Ratio                       ((%))
import           Data.Traversable                 (for, traverse)
import           Data.Tuple                       (fst, snd, uncurry)
import           Data.Zip                         (zipWith)
import           Prelude                          (Integer, error)
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp, inv)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Utils           (zipWithM)
import           ZkFold.Base.Data.Vector
import           ZkFold.Prelude                   (iterateM, length)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators (expansion, log2, maxBitsPerFieldElement, splitExpansion)
import           ZkFold.Symbolic.Data.Ord         (blueprintGE)
import           ZkFold.Symbolic.Interpreter
import           ZkFold.Symbolic.MonadCircuit     (MonadCircuit, newAssigned)

type Size = 7

-- | Foreign-field arithmetic based on https://cr.yp.to/papers/mmecrt.pdf
newtype FFA (p :: Natural) c = FFA (c (Vector Size))

deriving newtype instance SymbolicData (FFA p c)
deriving newtype instance NFData (c (Vector Size)) => NFData (FFA p c)
deriving newtype instance Haskell.Show (c (Vector Size)) => Haskell.Show (FFA p c)

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

toZp :: forall p a. (Arithmetic a, KnownNat p) => Vector Size a -> Zp p
toZp = fromConstant . impl
  where
    mods = coprimes @a
    binary g m = (fromConstant g * 2 ^ sigma) `div` fromConstant m
    impl xs =
      let gs0 = zipWith (\x y -> toConstant x * y) xs $ minv @a
          gs = zipWith mod gs0 mods
          residue = floorN ((3 % 4) + sum (zipWith binary gs mods) % (2 ^ sigma))
       in vectorDotProduct gs (mis @a @p) -! mprod @a @p * residue

fromZp :: forall p a. Arithmetic a => Zp p -> Vector Size a
fromZp = (\(FFA (Interpreter xs) :: FFA p (Interpreter a)) -> xs) . fromConstant

condSubOF :: forall i a m . MonadCircuit i a m => Natural -> i -> m (i, i)
condSubOF m i = do
  z <- newAssigned zero
  o <- newAssigned one
  let bm = (\x -> if x Haskell.== 0 then z else o) <$> (binaryExpansion m ++ [0])
  bi <- expansion (length bm) i
  ovf <- blueprintGE (Haskell.reverse bi) (Haskell.reverse bm)
  res <- newAssigned (($ i) - ($ ovf) * fromConstant m)
  return (res, ovf)

condSub :: MonadCircuit i a m => Natural -> i -> m i
condSub m x = fst <$> condSubOF m x

smallCut :: forall i a m. (Arithmetic a, MonadCircuit i a m) => Vector Size i -> m (Vector Size i)
smallCut = zipWithM condSub $ coprimes @a

bigSub :: (Arithmetic a, MonadCircuit i a m) => Natural -> i -> m i
bigSub m j = trimPow j >>= trimPow >>= condSub m
  where
    s = Haskell.ceiling (log2 m) :: Natural
    trimPow i = do
      (l, h) <- splitExpansion s s i
      newAssigned (($ l) + ($ h) * fromConstant ((2 ^ s) -! m))

bigCut :: forall i a m. (Arithmetic a, MonadCircuit i a m) => Vector Size i -> m (Vector Size i)
bigCut = zipWithM bigSub $ coprimes @a

cast :: forall p i a m. (KnownNat p, Arithmetic a, MonadCircuit i a m) => Vector Size i -> m (Vector Size i)
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

mul :: forall p i a m. (KnownNat p, Arithmetic a, MonadCircuit i a m) => Vector Size i -> Vector Size i -> m (Vector Size i)
mul xs ys = zipWithM (\i j -> newAssigned (\w -> w i * w j)) xs ys >>= bigCut >>= cast @p

natPowM :: Monad m => (a -> a -> m a) -> m a -> Natural -> a -> m a
natPowM _ z 0 _ = z
natPowM _ _ 1 x = pure x
natPowM f z n x
  | Haskell.even n    = natPowM f z (n `div` 2) x >>= \y -> f y y
  | Haskell.otherwise = natPowM f z (n -! 1) x >>= f x

oneM :: MonadCircuit i a m => m (Vector Size i)
oneM = pure <$> newAssigned (const one)

instance (KnownNat p, Arithmetic a) => ToConstant (FFA p (Interpreter a)) where
  type Const (FFA p (Interpreter a)) = Zp p
  toConstant (FFA (Interpreter rs)) = toZp rs

instance (FromConstant a (Zp p), Symbolic c) => FromConstant a (FFA p c) where
  fromConstant = FFA . embed . impl . toConstant . (fromConstant :: a -> Zp p)
    where
      impl :: Natural -> Vector Size (BaseField c)
      impl x = fromConstant . (x `mod`) <$> coprimes @(BaseField c)

instance {-# OVERLAPPING #-} FromConstant (FFA p c) (FFA p c)

instance {-# OVERLAPPING #-} (KnownNat p, Symbolic c) => Scale (FFA p c) (FFA p c)

instance (KnownNat p, Symbolic c) => MultiplicativeSemigroup (FFA p c) where
  FFA x * FFA y =
    FFA $ symbolic2F x y (\u v -> fromZp (toZp u * toZp v :: Zp p)) (mul @p)

instance (KnownNat p, Symbolic c) => Exponent (FFA p c) Natural where
  FFA x ^ a =
    FFA $ symbolicF x (\v -> fromZp (toZp v ^ a :: Zp p)) $ natPowM (mul @p) oneM a

instance (KnownNat p, Symbolic c) => MultiplicativeMonoid (FFA p c) where
  one = fromConstant (one :: Zp p)

instance (KnownNat p, Symbolic c) => AdditiveSemigroup (FFA p c) where
  FFA x + FFA y =
    FFA $ symbolic2F x y (\u v -> fromZp (toZp u + toZp v :: Zp p)) $ \xs ys ->
      zipWithM (\i j -> newAssigned (\w -> w i + w j)) xs ys >>= smallCut >>= cast @p

instance (KnownNat p, Scale a (Zp p), Symbolic c) => Scale a (FFA p c) where
  scale k x = fromConstant (scale k one :: Zp p) * x

instance (KnownNat p, Symbolic c) => AdditiveMonoid (FFA p c) where
  zero = fromConstant (zero :: Zp p)

instance (KnownNat p, Symbolic c) => AdditiveGroup (FFA p c) where
  negate (FFA x) = FFA $ symbolicF x (fromZp . negate . toZp @p) $ \xs -> do
    let cs = coprimes @(BaseField c)
    ys <- zipWithM (\i m -> newAssigned $ fromConstant m - ($ i)) xs cs
    cast @p ys

instance (KnownNat p, Symbolic c) => Semiring (FFA p c)

instance (KnownNat p, Symbolic c) => Ring (FFA p c)

instance (Prime p, Symbolic c) => Exponent (FFA p c) Integer where
  x ^ a = x `intPowF` (a `mod` fromConstant (value @p -! 1))

instance (Prime p, Symbolic c) => Field (FFA p c) where
  finv (FFA x) =
    FFA $ symbolicF x (fromZp . finv @(Zp p) . toZp)
      $ natPowM (mul @p) oneM (value @p -! 2)

instance Finite (Zp p) => Finite (FFA p b) where
  type Order (FFA p b) = p
