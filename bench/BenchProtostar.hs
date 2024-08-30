{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}

module Main where

import           Control.DeepSeq                                     (force)
import           Control.Exception                                   (evaluate)
import           Control.Monad                                       (replicateM)
import           Data.Time.Clock                                     (getCurrentTime)
import           Prelude                                             hiding (divMod, not, sum, (&&), (*), (+), (-), (/),
                                                                      (^), (||))
import           System.Random                                       (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar
import           ZkFold.Base.Protocol.ARK.Protostar.Commit
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement)
import           ZkFold.Symbolic.Data.UInt


fact
    :: forall a n c
    .  Arithmetic a
    => c ~ ArithmeticCircuit a (Vector n)
    => KnownNat n
    => MultiplicativeSemigroup (FieldElement c)
    => Vector n (FieldElement c) -> Vector n (FieldElement c)
fact v = V.generate (\i -> if i == 0 then v V.!! 0 * v V.!! 1 else v V.!! 0)

-- | Generate random addition circuit of given size
--
input
    :: forall n k p
    .  KnownNat n
    => KnownNat k
    => PrimeField (Zp p)
    => IO (Natural, (Vector n (Zp p)))
input = do
    v <- V.unsafeToVector <$> replicateM (fromIntegral $ value @k) (toZp <$> randomIO)

    evaluate . force $ (value @k, v)

benchOps
    :: forall n k p
    .  KnownNat n
    => KnownNat k
    => PrimeField (Zp p)
    => Benchmark
benchOps = env (input @n @k) $ \ ~inp ->
    bench ("Folding a function of size " <> show (value @n) <> " arguments with " <> show (value @k) <> " iterations") $
        nf (\(iter, inp) -> fold @(Zp p) @n @(Point BLS12_381_G1) (fact @(Zp p) @n) iter inp) inp

foldFact :: Natural -> Vector 2 Natural -> FoldResult 2 (Point BLS12_381_G1) (Zp BLS12_381_Scalar)
foldFact iter inp = fold (fact @(Zp BLS12_381_Scalar) @2) iter (toZp . fromIntegral <$> inp)

main :: IO ()
main = do
    print $ foldFact 1 (V.unsafeToVector [1, 2])
    defaultMain
      [ benchOps @2 @32  @BLS12_381_Scalar
      , benchOps @2 @64  @BLS12_381_Scalar
      , benchOps @2 @128 @BLS12_381_Scalar
      ]

