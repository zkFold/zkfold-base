{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           Data.Map                                    (fromList, keys)
import           GHC.Generics
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), (==>))
import           Tests.Plonk                                 (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Base.Data.Vector                     (Vector (..))
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..))
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Types                       (Symbolic)

lockedByTxId :: forall a a' . (Symbolic a , FromConstant a' a) => a' -> Par1 a -> Bool a
lockedByTxId targetValue txId = txId == Par1 (fromConstant targetValue)

testSameValue :: Fr -> Haskell.Bool
testSameValue targetValue =
    let ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) targetValue)
        b  = acValue (applyArgs ac [targetValue])
    in b Haskell.== one

testDifferentValue :: Fr -> Fr -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let ac = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) targetValue)
        b  = acValue (applyArgs ac [otherValue])
    in b Haskell.== zero

testZKP :: Fr -> PlonkProverSecret -> Fr -> Haskell.Bool
testZKP x ps targetValue =
    let ac      = compile @Fr (lockedByTxId @(ArithmeticCircuit Fr) targetValue)
        (omega, k1, k2) = getParams 5
        inputs  = fromList [(1, targetValue), (acOutput ac, 1)]
        plonk   = Plonk @32 omega k1 k2 (Vector @2 $ keys inputs) ac x
        setupP  = setupProve @PlonkBS plonk
        setupV  = setupVerify @PlonkBS plonk
        witness = (PlonkWitnessInput inputs, ps)
        (input, proof) = prove @PlonkBS setupP witness

    in verify @PlonkBS setupV input proof

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x Haskell./= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test" $ do
        it "should pass" $ property testZKP
