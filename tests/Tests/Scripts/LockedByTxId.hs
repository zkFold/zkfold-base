{-# LANGUAGE TypeApplications #-}

module Tests.Scripts.LockedByTxId (specLockedByTxId) where

import           GHC.Generics
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..))
import           Data.Map                                    (fromList, keys)
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (describe, hspec, it)
import           Test.QuickCheck                             (Testable (..), (==>))
import           Tests.Plonk                                 (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Base.Data.Vector                     (Vector (..))
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..))
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Cardano.Types               (TxId (..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Types                       (Symbolic)

lockedByTxId :: forall a a' . (Symbolic a , FromConstant a' a) => TxId a' -> TxId a -> U1 a -> Bool a
lockedByTxId (TxId targetId) (TxId txId) _ = Par1 txId == Par1 (fromConstant targetId)

testArithmetization1 :: Fr -> Haskell.Bool
testArithmetization1 targetId =
    let ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) (TxId targetId))
        b  = acValue (applyArgs ac [targetId])
    in b Haskell.== one

testArithmetization2 :: Fr -> Fr -> Haskell.Bool
testArithmetization2 targetId txId =
    let ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) (TxId targetId))
        b  = acValue (applyArgs ac [txId])
    in b Haskell.== zero

testZKP :: Fr -> PlonkProverSecret -> Fr -> Haskell.Bool
testZKP x ps targetId =
    let ac      = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) (TxId targetId))

        (omega, k1, k2) = getParams 5
        inputs  = fromList [(1, targetId), (acOutput ac, 1)]
        plonk   = Plonk @32 omega k1 k2 (Vector @2 $ keys inputs) ac x
        setupP  = setupProve @PlonkBS plonk
        setupV  = setupVerify @PlonkBS plonk
        witness = (PlonkWitnessInput inputs, ps)
        (input, proof) = prove @PlonkBS setupP witness

    in verify @PlonkBS setupV input proof

specLockedByTxId :: IO ()
specLockedByTxId = hspec $ do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testArithmetization1
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x Haskell./= y ==> testArithmetization2 x y
    describe "LockedByTxId ZKP test" $ do
        it "should pass" $ property testZKP
