{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE ViewPatterns                 #-}

module Main where

import           Control.DeepSeq                             (NFData (..), force)
import           Control.Exception                           (evaluate)
import           Control.Monad                               (forM_, replicateM)
import qualified Data.STRef                                  as ST
import qualified Data.Vector                                 as V
import qualified Data.Vector.Mutable                         as VM
import           GHC.Generics
import           Prelude                                     hiding (sum, (*), (+), (-), (/), (^))
import qualified Prelude                                     as P
import           System.Random                               (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.Polynomials.Univariate  (Poly (..), removeZeros, toPoly)
import           ZkFold.Prelude                              (zipWithDefault)




deriving instance Generic (Poly c)
deriving instance (Generic c, NFData c) => NFData (Poly c)
deriving instance Generic BLS12_381_Scalar
deriving instance NFData BLS12_381_Scalar

-- | Only for testing DFT with smaller numbers which can be easily calculated by hand for cross-check.
-- DFT of a polynomial of length n requires calculating primitive roots of unity of order n.
-- Choosing 17 allows us to calculate DFT of polynomials of length 2, 4, 8 and 16 as all these numbers divide 17 - 1.
data P17
    deriving (Generic, NFData)
instance Finite P17 where
    order = 17
instance Prime P17

-- | Generate random polynomials of given size
--
polynomials :: Int -> IO (Poly (Zp BLS12_381_Scalar), Poly (Zp BLS12_381_Scalar))
polynomials size = do
    coeffs1 <- replicateM size (toZp <$> randomIO)
    coeffs2 <- replicateM size (toZp <$> randomIO)
    evaluatedCoeffs1 <- evaluate . force . V.fromList $ coeffs1
    evaluatedCoeffs2 <- evaluate . force . V.fromList $ coeffs2
    pure (toPoly evaluatedCoeffs1, toPoly evaluatedCoeffs2)

sizes :: [Int]
sizes = [1, 2, 3] <> (((4 :: Int) P.^) <$> [1..5 :: Int]) <> ((( 2 :: Int) P.^) <$> [11..13 :: Int])

ops :: [(String, Poly (Zp BLS12_381_Scalar) -> Poly (Zp BLS12_381_Scalar) -> Poly (Zp BLS12_381_Scalar))]
ops = [ ("Vector multiplication", mulVec)
      , ("Karatsuba multiplication", mulKaratsuba)
      , ("DFT multiplication", mulDft)
      , ("Naive multiplication", mulNaive)
      ]

benchOps :: Int -> [(String, Poly (Zp BLS12_381_Scalar) -> Poly (Zp BLS12_381_Scalar) -> Poly (Zp BLS12_381_Scalar))] -> Benchmark
benchOps size testOps = env (polynomials size) $ \ ~(p1, p2) ->
    bgroup ("Multiplying polynomials of size " <> show size) $
            flip fmap testOps $ \(desc, op) -> bench desc $ nf (uncurry op) (p1, p2)

main :: IO ()
main = do
  forM_ sizes $ \s -> do
      (p1, p2) <- polynomials s
      putStrLn $ "Size " <> show s
      let ref = p1 `mulNaive` p2
      putStrLn $ "Karatsuba\t" <> show (ref == p1 `mulKaratsuba` p2)
      putStrLn $ "Vector\t\t"  <> show (ref == p1 `mulVec` p2)
      putStrLn $ "DFT\t\t"     <> show (ref == p1 `mulDft` p2)
  defaultMain $ flip fmap sizes $ \s -> benchOps s ops

-- | Naive vector multiplication, O(n^2)
--
vmul :: forall a. Field a => V.Vector a -> V.Vector a -> V.Vector a
vmul v1 v2 = result
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

mulVec :: forall a. Field a => Poly a -> Poly a -> Poly a
mulVec (P v1) (P v2) = P (vmul v1 v2)

-- | Adaptation of Karatsuba's algorithm. O(n^log_2(3))
--
mulKaratsuba :: forall a. (Field a, Eq a) => Poly a -> Poly a -> Poly a
mulKaratsuba (P v1) (P v2) = removeZeros $ P result
  where
    l = max (V.length v1) (V.length v2)
    p = ceiling @Double @Integer $ logBase 2 (fromIntegral l)

    pad = 2 P.^ p

    result = kmul (v1 V.++ V.replicate (pad - V.length v1) zero) (v2 V.++ V.replicate (pad - V.length v2) zero)

kmul :: forall a. Field a => V.Vector a -> V.Vector a -> V.Vector a
kmul v1 v2
  | len == 1 = V.zipWith (*) v1 v2
  | otherwise = result
  where
    len = V.length v1

    n = len `div` 2

    (b, a) = V.splitAt n v1

    (d, c) = V.splitAt n v2

    ac = kmul a c
    bd = kmul b d

    apb = V.zipWith (+) a b
    cpd = V.zipWith (+) c d

    abcd = kmul apb cpd

    mid = V.zipWith3 (\x y z -> x - y - z) abcd ac bd
    result = V.generate (2 * len - 1) ix2v

    ix2v ix
      | ix < n = bd `V.unsafeIndex` ix
      | ix < 2 * n - 1 = bd `V.unsafeIndex` ix + mid `V.unsafeIndex` (ix - n)
      | ix == 2 * n - 1 = mid `V.unsafeIndex` (n - 1)
      | ix < 3 * n - 1 = mid `V.unsafeIndex` (ix - n) + ac `V.unsafeIndex` (ix - 2 * n)
      | otherwise = ac `V.unsafeIndex` (ix - 2 * n)

-- DFT multiplication of vectors. O(nlogn)
--
mulDft :: forall a . (Field a, Eq a) => Poly a -> Poly a -> Poly a
mulDft (P v1) (P v2) = removeZeros $ P result
  where
    l = max (V.length v1) (V.length v2)
    p = (ceiling @Double $ logBase 2 (fromIntegral l)) + 1

    pad = 2 P.^ p

    result = dmul @a p (v1 V.++ V.replicate (pad - V.length v1) zero) (v2 V.++ V.replicate (pad - V.length v2) zero)

dmul :: forall a . (Field a, Eq a) => Integer -> V.Vector a -> V.Vector a -> V.Vector a
dmul n v1 v2 = fmap (* nInv) $ genericDft n w2nInv cImage
  where
    w2n :: a
    w2n = case rootOfUnity $ fromIntegral n of
            Just a -> a
            _      -> undefined

    w2nInv = one / w2n

    nInv = one / fromConstant ((2 :: Integer) P.^ n)

    v1Image = genericDft n w2n v1
    v2Image = genericDft n w2n v2

    cImage = V.zipWith (*) v1Image v2Image

genericDft
    :: forall a
     . Field a
    => Eq a
    => Integer
    -> a
    -> V.Vector a
    -> V.Vector a
genericDft 0 _  v = v
genericDft n wn v = V.create $ do
    result <- VM.new (2 P.^ n)
    wRef <- ST.newSTRef one
    forM_ [0 .. halfLen - 1] $ \k -> do
        w <- ST.readSTRef wRef
        VM.write result k             $ a0Hat `V.unsafeIndex` k + w * a1Hat `V.unsafeIndex` k
        VM.write result (k + halfLen) $ a0Hat `V.unsafeIndex` k - w * a1Hat `V.unsafeIndex` k
        ST.modifySTRef wRef (*wn)
    pure result
  where
    a0 = V.ifilter (\i _ -> i `mod` 2 == 0) v
    a1 = V.ifilter (\i _ -> i `mod` 2 == 1) v

    a0Hat = genericDft (n - 1) (wn * wn) a0
    a1Hat = genericDft (n - 1) (wn * wn) a1

    halfLen = 2 P.^ (n - 1)

mulNaive :: (Eq a, Field a) => Poly a -> Poly a -> Poly a
mulNaive (P v1) (P v2) = removeZeros $ P $ V.fromList $ go (V.toList v1) (V.toList v2)
    where
        go [] _      = []
        go (x:xs) ys = zipWithDefault (+) zero zero (map (x *) ys) (zero : go xs ys)
