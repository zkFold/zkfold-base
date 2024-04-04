{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Polynomials.Univariate where

import qualified Data.Vector                      as V
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (Num (..), drop, length, product, replicate, sum, take, (/), (^))
import qualified Prelude                          as P
import           Test.QuickCheck                  (Arbitrary (..), chooseInt)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.DFT    (genericDft)
import           ZkFold.Base.Algebra.Basic.Number

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

        lPadded = l V.++ V.replicate (len P.- V.length l) zero
        rPadded = r V.++ V.replicate (len P.- V.length r) zero

instance Scale c' c => Scale c' (Poly c) where
    scale c' (P v) = P $ V.map (scale c') v

instance (Ring c, Eq c) => AdditiveMonoid (Poly c) where
    zero = P V.empty

instance (Ring c, Eq c) => AdditiveGroup (Poly c) where
    negate (P cs) = P $ fmap negate cs

instance (Field c, Eq c) => MultiplicativeSemigroup (Poly c) where
    -- | If it is possible to calculate a primitive root of unity in the field, proceed with FFT multiplication.
    -- Otherwise default to Karatsuba multiplication for polynomials of degree higher than 64 or use naive multiplication otherwise.
    -- 64 is a threshold determined by benchmarking.
    P l * P r = removeZeros $ P $ mulAdaptive l r

padVector :: forall a . Ring a => V.Vector a -> Int -> V.Vector a
padVector v l
  | V.length v == l = v
  | otherwise = v V.++ V.replicate (l P.- V.length v) zero

mulAdaptive :: forall c . Field c => V.Vector c -> V.Vector c -> V.Vector c
mulAdaptive l r
      | V.null l = V.empty
      | V.null r = V.empty
      | otherwise =
          case (maybeW2n, len <= 64) of
            (_, True)        -> mulVector l r
            (Just w2n, _)    -> mulDft (p + 1) w2n lPaddedDft rPaddedDft
            (Nothing, False) -> mulKaratsuba lPaddedKaratsuba rPaddedKaratsuba
        where
            len :: Int
            len = max (V.length l) (V.length r)

            p :: Integer
            p = ceiling @Double $ logBase 2 (fromIntegral len)

            padKaratsuba :: Int
            padKaratsuba = 2 P.^ p

            padDft :: Int
            padDft = 2 P.* padKaratsuba

            lPaddedKaratsuba, rPaddedKaratsuba :: V.Vector c
            lPaddedKaratsuba = padVector l padKaratsuba
            rPaddedKaratsuba = padVector r padKaratsuba

            lPaddedDft, rPaddedDft :: V.Vector c
            lPaddedDft = padVector l padDft
            rPaddedDft = padVector r padDft

            maybeW2n :: Maybe c
            maybeW2n = rootOfUnity $ fromIntegral (p P.+ 1)

mulDft :: forall c . Field c => Integer -> c -> V.Vector c -> V.Vector c -> V.Vector c
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
    c = (* nInv) <$> genericDft p w2nInv cImage

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

    partLen :: Int
    partLen = len P.- 1


    ac, bd :: V.Vector a
    ac = padVector (mulAdaptive a c) partLen
    bd = padVector (mulAdaptive b d) partLen

    apb, cpd :: V.Vector a
    apb = V.zipWith (+) a b
    cpd = V.zipWith (+) c d

    abcd :: V.Vector a
    abcd = mulAdaptive apb cpd

    mid :: V.Vector a
    mid = V.zipWith3 (\x y z -> x - y - z) (padVector abcd partLen) (padVector ac partLen) (padVector bd partLen)

    result :: V.Vector a
    result = V.generate (2 P.* len P.- 1) ix2v

    ix2v :: Int -> a
    ix2v ix
      | ix < n = bd `V.unsafeIndex` ix
      | ix < 2 P.* n P.- 1 = bd `V.unsafeIndex` ix + mid `V.unsafeIndex` (ix P.- n)
      | ix == 2 P.* n P.- 1 = mid `V.unsafeIndex` (n P.- 1)
      | ix < 3 P.* n P.- 1 = mid `V.unsafeIndex` (ix P.- n) + ac `V.unsafeIndex` (ix P.- 2 P.* n)
      | otherwise = ac `V.unsafeIndex` (ix P.- 2 P.* n)

mulVector :: forall a. Field a => V.Vector a -> V.Vector a -> V.Vector a
mulVector v1 v2 = result
  where
    len1 = V.length v1
    len2 = V.length v2

    result = V.generate (len1 P.+ len2 P.- 1) ix2v

    ix2v :: Int -> a
    ix2v ix = ix2v' start1 start2 zero
      where
        start1 = min ix (len1 P.- 1)
        start2 = max 0 (ix P.- len1 P.+ 1)

    ix2v' :: Int -> Int -> a -> a
    ix2v' (-1) _ accum                = accum
    ix2v' _ ((== len2) -> True) accum = accum
    ix2v' i j accum                   = ix2v' (i P.- 1) (j P.+ 1) (accum + v1 `V.unsafeIndex` i * v2 `V.unsafeIndex` j)

instance (Field c, Eq c) => Exponent Natural (Poly c) where
    (^) = natPow

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
newtype PolyVec c (size :: Natural) = PV (V.Vector c)
    deriving (Eq, Show)

toPolyVec :: forall c size . (Ring c, KnownNat size) => V.Vector c -> PolyVec c size
toPolyVec = PV . V.take (fromIntegral (value @size)) . addZeros @c @size

fromPolyVec :: PolyVec c size -> V.Vector c
fromPolyVec (PV cs) = cs

poly2vec :: forall c size . (Ring c, KnownNat size) => Poly c -> PolyVec c size
poly2vec (P cs) = toPolyVec cs

vec2poly :: (Ring c, Eq c) => PolyVec c size -> Poly c
vec2poly (PV cs) = removeZeros $ P cs

instance Scale c' c => Scale c' (PolyVec c size) where
    scale c' (PV p) = PV $ V.map (scale c') p

instance Ring c => AdditiveSemigroup (PolyVec c size) where
    PV l + PV r = PV $ V.zipWith (+) l r

instance (Ring c, KnownNat size) => AdditiveMonoid (PolyVec c size) where
    zero = PV $ V.replicate (fromIntegral (value @size)) zero

instance (Ring c, KnownNat size) => AdditiveGroup (PolyVec c size) where
    negate (PV cs) = PV $ fmap negate cs

instance (Field c, KnownNat size, Eq c) => Exponent Natural (PolyVec c size) where
    (^) = natPow

-- TODO (Issue #18): check for overflow
instance (Field c, KnownNat size, Eq c) => MultiplicativeSemigroup (PolyVec c size) where
    l * r = poly2vec $ vec2poly l * vec2poly r

instance (Field c, KnownNat size, Eq c) => MultiplicativeMonoid (PolyVec c size) where
    one = PV $ V.singleton one V.++ V.replicate (fromIntegral (value @size -! 1)) zero

instance (Ring c, Arbitrary c, KnownNat size) => Arbitrary (PolyVec c size) where
    arbitrary = toPolyVec <$> V.replicateM (fromIntegral $ value @size) arbitrary

-- p(x) = a0 + a1 * x
polyVecLinear :: forall c size . (Ring c, KnownNat size) => c -> c -> PolyVec c size
polyVecLinear a0 a1 = PV $ V.fromList [a0, a1] V.++ V.replicate (fromIntegral $ value @size -! 2) zero

-- p(x) = a0 + a1 * x + a2 * x^2
polyVecQuadratic :: forall c size . (Ring c, KnownNat size) => c -> c -> c -> PolyVec c size
polyVecQuadratic a0 a1 a2 = PV $ V.fromList [a0, a1, a2] V.++ V.replicate (fromIntegral $ value @size -! 3) zero

scalePV :: Ring c => c -> PolyVec c size -> PolyVec c size
scalePV c (PV as) = PV $ fmap (*c) as

evalPolyVec :: Ring c => PolyVec c size -> c -> c
evalPolyVec (PV cs) x = sum $ V.zipWith (*) cs $ fmap (x^) (V.generate (V.length cs) (fromIntegral @_ @Natural))

castPolyVec :: forall c size size' . (Ring c, KnownNat size, KnownNat size', Eq c) => PolyVec c size -> PolyVec c size'
castPolyVec (PV cs)
    | value @size <= value @size'                             = toPolyVec cs
    | all (== zero) (V.drop (fromIntegral (value @size')) cs) = toPolyVec cs
    | otherwise = error "castPolyVec: Cannot cast polynomial vector to smaller size!"

-- p(x) = x^n - 1
polyVecZero :: forall c size size' . (Field c, KnownNat size, KnownNat size', Eq c) => PolyVec c size'
polyVecZero = poly2vec $ scaleP one (value @size) one - one

-- L_i(x) : p(omega^i) = 1, p(omega^j) = 0, j /= i, 1 <= i <= n, 1 <= j <= n
polyVecLagrange :: forall c size size' . (Field c, Eq c, KnownNat size, KnownNat size') =>
    Natural -> c -> PolyVec c size'
polyVecLagrange i omega = scalePV (omega^i / fromConstant (value @size)) $ (polyVecZero @c @size @size' - one) `polyVecDiv` polyVecLinear (negate $ omega^i) one

-- p(x) = c_1 * L_1(x) + c_2 * L_2(x) + ... + c_n * L_n(x)
polyVecInLagrangeBasis :: forall c size size' . (Field c, Eq c, KnownNat size, KnownNat size') =>
    c -> PolyVec c size -> PolyVec c size'
polyVecInLagrangeBasis omega (PV cs) =
    let ls = fmap (\i -> polyVecLagrange @c @size @size' i omega) (V.generate (V.length cs) (fromIntegral . succ))
    in sum $ V.zipWith scalePV cs ls

polyVecGrandProduct :: forall c size . (Field c, KnownNat size) =>
    PolyVec c size -> PolyVec c size -> PolyVec c size -> c -> c -> PolyVec c size
polyVecGrandProduct (PV as) (PV bs) (PV sigmas) beta gamma =
    let ps = fmap (+ gamma) (V.zipWith (+) as (fmap (* beta) bs))
        qs = fmap (+ gamma) (V.zipWith (+) as (fmap (* beta) sigmas))
        zs = fmap (product . flip V.take (V.zipWith (/) ps qs)) (V.generate (fromIntegral (value @size)) id)
    in PV zs

polyVecDiv :: forall c size . (Field c, KnownNat size, Eq c) =>
    PolyVec c size -> PolyVec c size -> PolyVec c size
polyVecDiv l r = poly2vec $ fst $ qr (vec2poly l) (vec2poly r)

-------------------------------- Helper functions --------------------------------

removeZeros :: (Ring c, Eq c) => Poly c -> Poly c
removeZeros (P cs)
  | V.null cs = P cs
  | otherwise = P $ V.take (1 P.+ traverseZeros startIx) cs
    where
        startIx :: Int
        startIx = V.length cs P.- 1

        traverseZeros :: Int -> Int
        traverseZeros 0
          | V.head cs == zero = -1
          | otherwise = 0
        traverseZeros n
          | cs `V.unsafeIndex` n == zero = traverseZeros (n P.- 1)
          | otherwise = n

addZeros :: forall c size . (Ring c, KnownNat size) => V.Vector c -> V.Vector c
addZeros cs = cs V.++ V.replicate (fromIntegral (value @size) P.- V.length cs) zero
