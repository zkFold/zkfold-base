{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}

module Main where

import           Control.DeepSeq                             (force)
import           Control.Exception                           (evaluate)
import           Control.Monad                               (replicateM)
import           Prelude                                     hiding (Bool (..), divMod, iterate, not, sum, (&&), (*),
                                                              (+), (-), (/), (^), (||))
import           System.Random                               (randomIO)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar
import           ZkFold.Symbolic.Class                       (Symbolic (..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

fact
    :: forall a n c
    .  c ~ ArithmeticCircuit a (Vector n)
    => KnownNat n
    => Symbolic c
    => MultiplicativeSemigroup (FieldElement c)
    => AdditiveSemigroup (FieldElement c)
    => Vector n (FieldElement c) -> Vector n (FieldElement c)
fact v = V.generate (\i -> if i == 0 then (v V.!! 0 * v V.!! 1) + fromConstant @Natural (42 :: Natural) else (v V.!! i) + (v V.!! 1 * v V.!! 2 * v V.!! i))

-- | Generate random addition circuit of given size
--
input
    :: forall n k p c
    .  KnownNat k
    => c ~ ArithmeticCircuit (Zp p) (Vector n)
    => PrimeField (Zp p)
    => IO (Natural, (Vector n (FieldElement c)))
input = do
    v <- V.unsafeToVector <$> replicateM (fromIntegral $ value @k) (toZp <$> randomIO)

    evaluate . force $ (value @k, fromConstant <$> v)

benchOps
    :: forall n k p c
    .  KnownNat n
    => KnownNat k
    => p ~ BLS12_381_Scalar
    => c ~ ArithmeticCircuit (Zp p) (Vector n)
    => Benchmark
benchOps = env (input @n @k) $ \ ~inp ->
    bench ("Folding a function of " <> show (value @n) <> " arguments with " <> show (value @k) <> " iterations") $
        nf (\(iter, initialInp) -> iterate @c @n @(Point (Ed25519 c)) @(Zp p) (fact @(Zp p) @n) initialInp iter) inp

foldFact :: ctx ~ ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 3)
         => Natural -> Vector 3 Natural -> ProtostarResult ctx 3 (Point (Ed25519 ctx)) (Zp BLS12_381_Scalar)
foldFact iter inp = iterate fact (fromConstant <$> inp) iter

main :: IO ()
main = do
    print $ foldFact 10 (V.unsafeToVector [1, 2, 3])
    defaultMain
      [ benchOps @3 @32  @BLS12_381_Scalar
      , benchOps @3 @64  @BLS12_381_Scalar
      , benchOps @3 @128 @BLS12_381_Scalar
      ]

