{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications             #-}

module Main where

import           Control.DeepSeq                             (NFData (..), force)
import           Control.Exception                           (evaluate)
import           Control.Monad                               (forM_, replicateM)
import qualified Data.Vector                                 as V
import           GHC.Generics
import           Prelude                                     hiding (sum, (*), (+), (-), (/), (^))
import qualified Prelude                                     as P
import           System.Random                               (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number            (Prime)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Prelude                              (zipWithDefault)

deriving instance Generic (Poly c)
deriving instance (Generic c, NFData c) => NFData (Poly c)

-- | Only for testing DFT with smaller numbers which can be easily calculated by hand for cross-check.
-- DFT of a polynomial of length n requires calculating primitive roots of unity of order n.
-- Choosing 17 allows us to calculate DFT of polynomials of length up to 256 and 16 as all these numbers divide 257 - 1.
instance Prime 257

-- | Generate random polynomials of given size
--
polynomials :: forall a. Prime a => Int -> IO (Poly (Zp a), Poly (Zp a))
polynomials size = do
    coeffs1 <- replicateM size (toZp @a <$> randomIO)
    coeffs2 <- replicateM size (toZp @a <$> randomIO)
    evaluatedCoeffs1 <- evaluate . force . V.fromList $ coeffs1
    evaluatedCoeffs2 <- evaluate . force . V.fromList $ coeffs2
    pure (toPoly evaluatedCoeffs1, toPoly evaluatedCoeffs2)

sizes :: [Int]
sizes = [1, 2, 3] <> (((4 :: Int) P.^) <$> [1..5 :: Int]) <> ((( 2 :: Int) P.^) <$> [11..13 :: Int])

ops :: (Eq a, Field a) => [(String, Poly a -> Poly a -> Poly a)]
ops = [ ("DFT multiplication", benchDft)
      , ("Adaptive multiplication", (*))
      , ("Karatsuba multiplication", benchKaratsuba)
      , ("Vector multiplication", benchVec)
      , ("Naive multiplication", benchNaive)
      ]

benchOps :: Prime a => Int -> [(String, Poly (Zp a) -> Poly (Zp a) -> Poly (Zp a))] -> Benchmark
benchOps size testOps = env (polynomials size) $ \ ~(p1, p2) ->
    bgroup ("Multiplying polynomials of size " <> show size) $
            flip fmap testOps $ \(desc, op) -> bench desc $ nf (uncurry op) (p1, p2)

main :: IO ()
main = do
  forM_ sizes $ \s -> do
      (p1, p2) <- polynomials @BLS12_381_Scalar s
      putStrLn $ "Size " <> show s
      let ref = p1 `benchNaive` p2
      putStrLn $ "Karatsuba\t" <> show (ref == p1 `benchKaratsuba` p2)
      putStrLn $ "Vector\t\t"  <> show (ref == p1 `benchVec` p2)
      putStrLn $ "DFT\t\t"     <> show (ref == p1 `benchDft` p2)
  defaultMain
      [ bgroup "Field with roots of unity"           $ flip fmap sizes $ \s -> benchOps @BLS12_381_Scalar s ops
      , bgroup "Field with roots of unity up to 256" $ flip fmap sizes $ \s -> benchOps @257 s $ tail ops
      , bgroup "Field without roots of unity"        $ flip fmap sizes $ \s -> benchOps @BLS12_381_Base s $ tail ops
      ]

-- | Naive vector multiplication, O(n^2)
--
benchVec :: forall a. Field a => Poly a -> Poly a -> Poly a
benchVec (P v1) (P v2) = P (mulVector v1 v2)

-- | Adaptation of Karatsuba's algorithm. O(n^log_2(3))
--
benchKaratsuba :: forall a. (Field a, Eq a) => Poly a -> Poly a -> Poly a
benchKaratsuba (P v1) (P v2) = removeZeros $ P result
  where
    l = max (V.length v1) (V.length v2)
    p = ceiling @Double @Integer $ logBase 2 (fromIntegral l)

    pad = 2 P.^ p

    result = mulKaratsuba (v1 V.++ V.replicate (pad P.- V.length v1) zero) (v2 V.++ V.replicate (pad P.- V.length v2) zero)

-- DFT multiplication of vectors. O(nlogn)
--
benchDft :: forall a . (Field a, Eq a) => Poly a -> Poly a -> Poly a
benchDft (P v1) (P v2) = removeZeros $ P result
  where
    l = max (V.length v1) (V.length v2)
    p = (ceiling @Double $ logBase 2 (fromIntegral l)) P.+ 1

    w2n :: a
    w2n = case rootOfUnity $ fromIntegral p of
            Just a -> a
            _      -> undefined

    pad = 2 P.^ p

    result = mulDft @a p w2n (v1 V.++ V.replicate (pad P.- V.length v1) zero) (v2 V.++ V.replicate (pad P.- V.length v2) zero)


benchNaive :: (Eq a, Field a) => Poly a -> Poly a -> Poly a
benchNaive (P v1) (P v2) = removeZeros $ P $ V.fromList $ go (V.toList v1) (V.toList v2)
    where
        go [] _      = []
        go (x:xs) ys = zipWithDefault (+) zero zero (map (x *) ys) (zero : go xs ys)
