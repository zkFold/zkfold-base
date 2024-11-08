module Tests.Protostar (specProtostar) where

import           GHC.Generics                                     (Par1(..))
import           Prelude                                          hiding (Num (..))
import           Test.Hspec                                       (it, describe, hspec)
import           Test.QuickCheck                                  (property)

import           ZkFold.Base.Algebra.Basic.Field                  (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381      (BLS12_381_Scalar, BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class          (Point)
import           ZkFold.Base.Algebra.Basic.Class                  (zero)
import           ZkFold.Base.Data.HFunctor                        (hmap)
import           ZkFold.Base.Data.Vector                          (Vector, item, singleton)
import           ZkFold.Base.Protocol.Protostar.Accumulator       (Accumulator(..), AccumulatorInstance(..))
import           ZkFold.Base.Protocol.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.Protostar.CommitOpen        (CommitOpen(..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir        (FiatShamir(..))
import           ZkFold.Base.Protocol.Protostar.NARK              (InstanceProofPair, instanceProof)
import           ZkFold.Symbolic.Compiler                         (ArithmeticCircuit, hlmap)
import           ZkFold.Symbolic.Data.FieldElement                (FieldElement(..))

type F = Zp BLS12_381_Scalar
type G = Point BLS12_381_G1
type PI = [F]
type M = [F]
type AC = ArithmeticCircuit F (Vector 1) (Vector 1)

testCircuit :: AC
testCircuit = hlmap (Par1 . item) $ hmap (\(Par1 x) -> singleton x) $ fromFieldElement zero

specialSoundProtocol :: FiatShamir F (CommitOpen M G AC)
specialSoundProtocol = FiatShamir $ CommitOpen testCircuit

initAccumulator :: Accumulator PI F G M
initAccumulator = Accumulator (AccumulatorInstance zero [zero] [] zero zero) []

testPublicInput :: PI
testPublicInput = zero

testInstanceProofPair :: InstanceProofPair PI G M
testInstanceProofPair = instanceProof @_ @F specialSoundProtocol testPublicInput

testAccumulator :: Accumulator PI F G M
testAccumulator = fst $ Acc.prover specialSoundProtocol initAccumulator testInstanceProofPair

testDeciderResult :: ([G], G)
testDeciderResult = decider specialSoundProtocol testAccumulator

specAccumulatorScheme :: IO ()
specAccumulatorScheme = hspec $ do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it  "must output zeros" $ do
                property $ testDeciderResult == (zero, zero)

specProtostar :: IO ()
specProtostar = do
    print testDeciderResult
    specAccumulatorScheme