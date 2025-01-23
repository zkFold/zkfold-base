{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Tests.Symbolic.Data.FFA (specFFA) where

import           Data.Function                               (($))
import           Data.List                                   ((++))
import           GHC.Generics                                (U1)
import           System.IO                                   (IO)
import           Test.Hspec                                  (describe, hspec)
import           Test.QuickCheck                             (Property, (===))
import           Tests.Symbolic.ArithmeticCircuit            (it)
import           Text.Show                                   (show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number            (Prime, value)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, exec)
import           ZkFold.Symbolic.Data.FFA                    (FFA (FFA))
import           ZkFold.Symbolic.Interpreter                 (Interpreter (Interpreter))

type Prime256_1 = 28948022309329048855892746252171976963363056481941560715954676764349967630337
type Prime256_2 = 28948022309329048855892746252171976963363056481941647379679742748393362948097

instance Prime Prime256_1
instance Prime Prime256_2

specFFA :: IO ()
specFFA = do
  specFFA' @BLS12_381_Scalar @Prime256_1
  specFFA' @BLS12_381_Scalar @Prime256_2

specFFA' :: forall p q. (PrimeField (Zp p), PrimeField (Zp q)) => IO ()
specFFA' = hspec $ do
  let q = value @q
  describe ("FFA " ++ show q ++ " specification") $ do
    it "FFA(Zp) embeds Zq" $ \(x :: Zp q) ->
      toConstant (fromConstant x :: FFA q (Interpreter (Zp p))) === x
    it "FFA(AC) embeds Zq" $ \(x :: Zp q) ->
      execAcFFA @p @q (fromConstant x) === x
    it "has zero" $ execAcFFA @p @q zero === execZpFFA @p @q zero
    it "has one" $ execAcFFA @p @q one === execZpFFA @p @q one
    it "adds correctly" $ isHom @p @q (+) (+)
    it "negates correctly" $ \(x :: Zp q) ->
      execAcFFA @p @q (negate $ fromConstant x) === execZpFFA @p @q (negate $ fromConstant x)
    it "multiplies correctly" $ isHom @p @q (*) (*)

execAcFFA :: (PrimeField (Zp p), PrimeField (Zp q)) => FFA q (ArithmeticCircuit (Zp p) U1 U1) -> Zp q
execAcFFA (FFA v) = execZpFFA $ FFA $ Interpreter (exec v)

execZpFFA :: (PrimeField (Zp p), PrimeField (Zp q)) => FFA q (Interpreter (Zp p)) -> Zp q
execZpFFA = toConstant

type Binary a = a -> a -> a
type Predicate a = a -> a -> Property

isHom :: (PrimeField (Zp p), PrimeField (Zp q)) => Binary (FFA q (Interpreter (Zp p))) -> Binary (FFA q (ArithmeticCircuit (Zp p) U1 U1)) -> Predicate (Zp q)
isHom f g x y = execAcFFA (fromConstant x `g` fromConstant y) === execZpFFA (fromConstant x `f` fromConstant y)
