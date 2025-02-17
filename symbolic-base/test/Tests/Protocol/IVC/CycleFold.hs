module Tests.Protocol.IVC.CycleFold where

import           Prelude                                           hiding (Bool (..), Num (..), pi, replicate, sum, (+))
import qualified Prelude                                           as Haskell
import           Test.Hspec                                        (Spec, describe, it, runIO)
import           Test.QuickCheck                                   (Arbitrary (..), property, withMaxSuccess)
import           Tests.Protocol.IVC.Types

import           ZkFold.Base.Algebra.Basic.Class                   (zero)
import           ZkFold.Base.Data.Vector                           (singleton)
import           ZkFold.Base.Protocol.IVC.Accumulator              (Accumulator (..), emptyAccumulator,
                                                                    emptyAccumulatorInstance)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme        (decider, prover, verifier)
import           ZkFold.Base.Protocol.IVC.Commit                   ()
import           ZkFold.Base.Protocol.IVC.CycleFold.ForeignContext (NativeOperation, opAccumulatorScheme, opPredicate,
                                                                    opProtocol)
import           ZkFold.Base.Protocol.IVC.CycleFold.Utils          (SecondaryGroup)
import           ZkFold.Base.Protocol.IVC.NARK                     (NARKInstanceProof (..), NARKProof (..),
                                                                    narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle                   (MiMCHash)
import           ZkFold.Base.Protocol.IVC.Predicate                (Predicate (..))
import           ZkFold.Symbolic.Compiler                          (acSizeN)

data AccumulationTestData = AccumulationTestData Haskell.Bool Haskell.Bool
    deriving Show
instance Arbitrary AccumulationTestData where
    arbitrary = do
        input   <- arbitrary
        payload <- arbitrary
        let
            accSheme = opAccumulatorScheme @MiMCHash @D @K @A
            sps      = opProtocol @MiMCHash @D @K @A

            narkIP :: NARKInstanceProof K NativeOperation SecondaryGroup W
            narkIP = narkInstanceProof sps input payload
            (acc@(Accumulator accX _), pf) = prover accSheme emptyAccumulator narkIP

            NARKInstanceProof input' (NARKProof proof _) = narkIP

            dRes = decider accSheme (fromWitness acc) == (singleton zero, zero)
            vRes = verifier accSheme (fromWitness input') (fromWitness <$> proof) emptyAccumulatorInstance (fromWitness <$> pf) == fromWitness accX
        return $ AccumulationTestData dRes vRes

specAccumulatorScheme :: Spec
specAccumulatorScheme = do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \(AccumulationTestData d _) -> d
        describe "verifier" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \(AccumulationTestData _ v) -> v

specCycleFold :: Spec
specCycleFold = do
    runIO $ print $ "ForeignContext circuit size: " ++ show (acSizeN $ predicateCircuit $ opPredicate @A)
    specAccumulatorScheme
