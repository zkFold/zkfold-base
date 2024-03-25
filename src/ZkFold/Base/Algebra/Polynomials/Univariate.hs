{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Polynomials.Univariate where

import qualified Data.Vector                     as V
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Num (..), drop, length, product, replicate, sum, take, (/), (^))
import qualified Prelude                         as P
import           Test.QuickCheck                 (Arbitrary (..), chooseInt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.DFT   (genericDft)

-------------------------------- Arbitrary degree polynomials --------------------------------

-- TODO (Issue #17): hide constructor
newtype Poly c = P (V.Vector c)
    deriving (Eq, Show)

toPoly :: (Ring c, Eq c) => V.Vector c -> Poly c
toPoly = removeZeros . P

fromPoly :: Poly c -> V.Vector c
fromPoly (P cs) = cs

instance (Ring c, Eq c) => AdditiveSemigroup (Poly c) where
    P l + P r = removeZeros $ P $ V.zipWith (+) lPadded rPadded
      where
        len = max (V.length l) (V.length r)

        lPadded = l V.++ V.replicate (len - V.length l) zero
        rPadded = r V.++ V.replicate (len - V.length r) zero

instance (Ring c, Eq c) => AdditiveMonoid (Poly c) where
    zero = P V.empty

instance (Ring c, Eq c) => AdditiveGroup (Poly c) where
    negate (P cs) = P $ fmap negate cs

instance (Field c, Eq c) => MultiplicativeSemigroup (Poly c) where
    -- | If it is possible to calculate a primitive root of unity in the field, proceed with FFT multiplication.
    -- Otherwise default to Karatsuba multiplication for polynomials of degree higher than 64 or use naive multiplication otherwise.
    -- 64 is a threshold determined by benchmarking.
    P l * P r
      | V.null l = P V.empty
      | V.null r = P V.empty
      | otherwise = removeZeros $ P $
          case (maybeW2n, len <= 64) of
            (Nothing, False) -> mulKaratsuba lPaddedKaratsuba rPaddedKaratsuba
            (Nothing, True)  -> mulVector l r
            (Just w2n, _)    -> mulDft (p + 1) w2n lPaddedDft rPaddedDft
        where
            len :: Int
            len = max (V.length l) (V.length r)

            p :: Integer
            p   = (ceiling @Double $ logBase 2 (fromIntegral len))

            padKaratsuba :: Int
            padKaratsuba = 2 P.^ p

            padDft :: Int
            padDft = 2 * padKaratsuba

            lPaddedKaratsuba, rPaddedKaratsuba :: V.Vector c
            lPaddedKaratsuba = l V.++ V.replicate (padKaratsuba - V.length l) zero
            rPaddedKaratsuba = r V.++ V.replicate (padKaratsuba - V.length r) zero

            lPaddedDft, rPaddedDft :: V.Vector c
            lPaddedDft = l V.++ V.replicate (padDft - V.length l) zero
            rPaddedDft = r V.++ V.replicate (padDft - V.length r) zero

            maybeW2n :: Maybe c
            maybeW2n = rootOfUnity $ fromIntegral (p + 1)

mulDft :: forall c . (Field c, Eq c) => Integer -> c -> V.Vector c -> V.Vector c -> V.Vector c
mulDft p w2n lPadded rPadded = c
  where
    pad :: Int
    pad = 2 P.^ p

    w2nInv :: c
    w2nInv = one / w2n

    nInv :: c
    nInv = one / fromConstant (fromIntegral @_ @Natural pad)

    v1Image, v2Image :: V.Vector c
    v1Image = genericDft p w2n lPadded
    v2Image = genericDft p w2n rPadded

    cImage :: V.Vector c
    cImage = V.zipWith (*) v1Image v2Image

    c :: V.Vector c
    c = fmap (* nInv) $ genericDft p w2nInv cImage

mulKaratsuba :: forall a. Field a => V.Vector a -> V.Vector a -> V.Vector a
mulKaratsuba v1 v2
  | len == 1 = V.zipWith (*) v1 v2
  | otherwise = result
  where
    len :: Int
    len = V.length v1

    n :: Int
    n = len `div` 2

    a, b, c, d :: V.Vector a
    (b, a) = V.splitAt n v1

    (d, c) = V.splitAt n v2

    ac, bd :: V.Vector a
    ac = mulKaratsuba a c
    bd = mulKaratsuba b d

    apb, cpd :: V.Vector a
    apb = V.zipWith (+) a b
    cpd = V.zipWith (+) c d

    abcd :: V.Vector a
    abcd = mulKaratsuba apb cpd

    mid :: V.Vector a
    mid = V.zipWith3 (\x y z -> x - y - z) abcd ac bd

    result :: V.Vector a
    result = V.generate (2 * len - 1) ix2v

    ix2v :: Int -> a
    ix2v ix
      | ix < n = bd `V.unsafeIndex` ix
      | ix < 2 * n - 1 = bd `V.unsafeIndex` ix + mid `V.unsafeIndex` (ix - n)
      | ix == 2 * n - 1 = mid `V.unsafeIndex` (n - 1)
      | ix < 3 * n - 1 = mid `V.unsafeIndex` (ix - n) + ac `V.unsafeIndex` (ix - 2 * n)
      | otherwise = ac `V.unsafeIndex` (ix - 2 * n)

mulVector :: forall a. Field a => V.Vector a -> V.Vector a -> V.Vector a
mulVector v1 v2 = result
  where
    len1 = V.length v1
    len2 = V.length v2

    result = V.generate (len1 + len2 - 1) ix2v

    ix2v :: Int -> a
    ix2v ix = ix2v' start1 start2 zero
      where
        start1 = min ix (len1 - 1)
        start2 = max 0 (ix - len1 + 1)

    ix2v' :: Int -> Int -> a -> a
    ix2v' (-1) _ accum                = accum
    ix2v' _ ((== len2) -> True) accum = accum
    ix2v' i j accum                   = ix2v' (i - 1) (j + 1) (accum + v1 `V.unsafeIndex` i * v2 `V.unsafeIndex` j)

instance (Field c, Eq c) => MultiplicativeMonoid (Poly c) where
    one = P $ V.singleton one

instance (Ring c, Arbitrary c, Eq c) => Arbitrary (Poly c) where
    arbitrary = fmap toPoly $ chooseInt (0, 128) >>= \n -> V.replicateM n arbitrary

lt :: Poly c -> c
lt (P cs) = V.last cs

deg :: Poly c -> Integer
-- | Degree of zero polynomial is `-1`
deg (P cs) = fromIntegral (V.length cs) - 1

scaleP :: Ring c => c -> Natural -> Poly c -> Poly c
scaleP a n (P cs) = P $ V.replicate (fromIntegral n) zero V.++ fmap (a *) cs

qr :: (Field c, Eq c) => Poly c -> Poly c -> (Poly c, Poly c)
qr a b = go a b zero
    where
        go x y q = if deg x < deg y then (q, x) else go x' y q'
            where
                c = lt x / lt y
                n = fromIntegral (deg x - deg y)
                -- ^ if `deg x < deg y`, `n` is not evaluated, so this would not error out
                x' = x - scaleP c n y
                q' = q + scaleP c n one

-- | Extended Euclidean algorithm.
eea :: (Field c, Eq c) => Poly c -> Poly c -> (Poly c, Poly c)
eea a b = go (a, one) (b, zero)
    where
        go (x, s) (y, t) = if deg y == -1 then (x, s) else go (y, t) (r, s - q * t)
            where
                (q, r) = qr x y

---------------------------------- Fixed degree polynomials ----------------------------------

-- TODO (Issue #17): hide constructor
newtype PolyVec c size = PV (V.Vector c)
    deriving (Eq, Show)

toPolyVec :: forall c size . (Ring c, Finite size) => V.Vector c -> PolyVec c size
toPolyVec = PV . V.take (fromIntegral (order @size)) . addZeros @c @size

fromPolyVec :: PolyVec c size -> V.Vector c
fromPolyVec (PV cs) = cs

poly2vec :: forall c size . (Ring c, Finite size) => Poly c -> PolyVec c size
poly2vec (P cs) = toPolyVec cs

vec2poly :: (Ring c, Eq c) => PolyVec c size -> Poly c
vec2poly (PV cs) = removeZeros $ P cs

instance Ring c => AdditiveSemigroup (PolyVec c size) where
    PV l + PV r = PV $ V.zipWith (+) l r

instance (Ring c, Finite size) => AdditiveMonoid (PolyVec c size) where
    zero = PV $ V.replicate (fromIntegral (order @size)) zero

instance (Ring c, Finite size) => AdditiveGroup (PolyVec c size) where
    negate (PV cs) = PV $ fmap negate cs

-- TODO (Issue #18): check for overflow
instance (Field c, Finite size, Eq c) => MultiplicativeSemigroup (PolyVec c size) where
    l * r = poly2vec $ vec2poly l * vec2poly r

instance (Field c, Finite size, Eq c) => MultiplicativeMonoid (PolyVec c size) where
    one = PV $ V.singleton one V.++ V.replicate (fromIntegral (order @size - 1)) zero

instance (Field c, Finite size, Eq c) => MultiplicativeGroup (PolyVec c size) where
    invert = undefined

    l / r = poly2vec $ fst $ qr (vec2poly l) (vec2poly r)

instance (Ring c, Arbitrary c, Finite size) => Arbitrary (PolyVec c size) where
    arbitrary = toPolyVec <$> V.replicateM (fromIntegral $ order @size) arbitrary

-- p(x) = a0 + a1 * x
polyVecLinear :: forall c size . (Ring c, Finite size) => c -> c -> PolyVec c size
polyVecLinear a0 a1 = PV $ V.fromList [a0, a1] V.++ V.replicate (fromIntegral $ order @size - 2) zero

-- p(x) = a0 + a1 * x + a2 * x^2
polyVecQuadratic :: forall c size . (Ring c, Finite size) => c -> c -> c -> PolyVec c size
polyVecQuadratic a0 a1 a2 = PV $ V.fromList [a0, a1, a2] V.++ V.replicate (fromIntegral $ order @size - 3) zero

scalePV :: Ring c => c -> PolyVec c size -> PolyVec c size
scalePV c (PV as) = PV $ fmap (*c) as

evalPolyVec :: Ring c => PolyVec c size -> c -> c
evalPolyVec (PV cs) x = sum $ V.zipWith (*) cs $ fmap (x^) (V.generate (V.length cs) (fromIntegral @_ @Integer))

castPolyVec :: forall c size size' . (Ring c, Finite size, Finite size', Eq c) => PolyVec c size -> PolyVec c size'
castPolyVec (PV cs)
    | order @size <= order @size'                             = toPolyVec cs
    | all (== zero) (V.drop (fromIntegral (order @size')) cs) = toPolyVec cs
    | otherwise = error "castPolyVec: Cannot cast polynomial vector to smaller size!"

-- p(x) = x^n - 1
polyVecZero :: forall c size size' . (Field c, Finite size, Finite size', Eq c) => PolyVec c size'
polyVecZero = poly2vec $ scaleP one (order @size) one - one

-- L_i(x) : p(omega^i) = 1, p(omega^j) = 0, j /= i, 1 <= i <= n, 1 <= j <= n
polyVecLagrange :: forall c size size' . (Field c, Eq c, Finite size, Finite size') =>
    Natural -> c -> PolyVec c size'
polyVecLagrange i omega = scalePV (omega^i / fromConstant (order @size)) $ (polyVecZero @c @size @size' - one) / polyVecLinear (negate $ omega^i) one

-- p(x) = c_1 * L_1(x) + c_2 * L_2(x) + ... + c_n * L_n(x)
polyVecInLagrangeBasis :: forall c size size' . (Field c, Eq c, Finite size, Finite size') =>
    c -> PolyVec c size -> PolyVec c size'
polyVecInLagrangeBasis omega (PV cs) =
    let ls = fmap (\i -> polyVecLagrange @c @size @size' i omega) (V.generate (V.length cs) (fromIntegral . succ))
    in sum $ V.zipWith scalePV cs ls

polyVecGrandProduct :: forall c size . (Field c, Finite size) =>
    PolyVec c size -> PolyVec c size -> PolyVec c size -> c -> c -> PolyVec c size
polyVecGrandProduct (PV as) (PV bs) (PV sigmas) beta gamma =
    let ps = fmap (+ gamma) (V.zipWith (+) as (fmap (* beta) bs))
        qs = fmap (+ gamma) (V.zipWith (+) as (fmap (* beta) sigmas))
        zs = fmap (product . flip V.take (V.zipWith (/) ps qs)) (V.generate (fromIntegral (order @size)) id)
    in PV zs

-------------------------------- Helper functions --------------------------------

removeZeros :: (Ring c, Eq c) => Poly c -> Poly c
removeZeros (P cs)
  | V.null cs = P cs
  | otherwise = P $ V.take (1 + traverseZeros startIx) cs
    where
        startIx :: Int
        startIx = V.length cs - 1

        traverseZeros :: Int -> Int
        traverseZeros 0
          | V.head cs == zero = -1
          | otherwise = 0
        traverseZeros n
          | cs `V.unsafeIndex` n == zero = traverseZeros (n - 1)
          | otherwise = n

addZeros :: forall c size . (Ring c, Finite size) => V.Vector c -> V.Vector c
addZeros cs = cs V.++ V.replicate (fromIntegral (order @size) - V.length cs) zero
