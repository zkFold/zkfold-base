{-# LANGUAGE TypeApplications #-}

module Tests.Scripts.LockedByTxId (specLockedByTxId) where

import Data.Map (fromList)
import Test.Hspec
import Test.QuickCheck
import Tests.Plonk (PlonkBS)
import ZkFold.Base.Algebra.Basic.Class (FromConstant (..))
import ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import ZkFold.Base.Protocol.ARK.Plonk (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..))
import ZkFold.Base.Protocol.ARK.Plonk.Internal (getParams)
import ZkFold.Base.Protocol.NonInteractiveProof (NonInteractiveProof (..))
import ZkFold.Symbolic.Cardano.Types (TxId (..))
import ZkFold.Symbolic.Compiler hiding (input)
import ZkFold.Symbolic.Data.Bool (Bool (..), BoolType (..))
import ZkFold.Symbolic.Data.Eq (Eq (..))
import ZkFold.Symbolic.Types (Symbolic)
import Prelude hiding (Bool, Eq (..), Num (..), Ord (..))
import qualified Prelude as Haskell

lockedByTxId :: forall a a'. (Symbolic a, FromConstant a' a) => TxId a' -> TxId a -> () -> Bool a
lockedByTxId (TxId targetId) (TxId txId) _ = txId == fromConstant targetId

testArithmetization1 :: Fr -> Haskell.Bool
testArithmetization1 targetId =
  let Bool ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) (TxId targetId)) :: Bool (ArithmeticCircuit Fr)
      b = Bool $ acValue (applyArgs ac [targetId])
   in b == true

testArithmetization2 :: Fr -> Fr -> Haskell.Bool
testArithmetization2 targetId txId =
  let Bool ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) (TxId targetId)) :: Bool (ArithmeticCircuit Fr)
      b = Bool $ acValue (applyArgs ac [txId])
   in b == false

testZKP :: Fr -> PlonkProverSecret -> Fr -> Haskell.Bool
testZKP x ps targetId =
  let Bool ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) (TxId targetId)) :: Bool (ArithmeticCircuit Fr)

      (omega, k1, k2) = getParams 5
      inputs = fromList [(1, targetId), (acOutput ac, 1)]
      plonk = Plonk omega k1 k2 inputs ac x
      s = setup @PlonkBS plonk
      w = (PlonkWitnessInput inputs, ps)
      (input, proof) = prove @PlonkBS s w
   in verify @PlonkBS s input proof

specLockedByTxId :: IO ()
specLockedByTxId = hspec $ do
  describe "LockedByTxId arithmetization test 1" $ do
    it "should pass" $ property testArithmetization1
  describe "LockedByTxId arithmetization test 2" $ do
    it "should pass" $ property $ \x y -> x /= y ==> testArithmetization2 x y
  describe "LockedByTxId ZKP test" $ do
    it "should pass" $ property testZKP
