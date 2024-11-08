{-# LANGUAGE AllowAmbiguousTypes #-}

module Tests.Protostar (specProtostar) where

import           Prelude                           hiding (Num (..))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector           (Vector, item, singleton)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement(..))
import ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import ZkFold.Base.Algebra.Basic.Field (Zp)
import GHC.Generics (Par1(..))
import ZkFold.Symbolic.Compiler (ArithmeticCircuit, hlmap)
import ZkFold.Base.Data.HFunctor (hmap)
import ZkFold.Base.Algebra.Basic.Class (one, zero, AdditiveMonoid)
import ZkFold.Base.Protocol.Protostar.Accumulator (Accumulator(..), AccumulatorInstance(..))
import ZkFold.Base.Protocol.Protostar.NARK (instanceProof, InstanceProofPair)
import ZkFold.Base.Protocol.Protostar.CommitOpen (CommitOpen(..))
import ZkFold.Base.Protocol.Protostar.FiatShamir (FiatShamir(..))
import Data.Kind (Type)
import ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol(..))
import ZkFold.Base.Protocol.Protostar.Oracle (RandomOracle)
import ZkFold.Base.Protocol.Protostar.Commit (HomomorphicCommit)

type F = Zp BLS12_381_Scalar
type AC = ArithmeticCircuit F (Vector 1) (Vector 1)

testCircuit :: AC
testCircuit = hlmap (Par1 . item) $ hmap (\(Par1 x) -> singleton x) $ fromFieldElement zero

specialSoundProtocol :: FiatShamir F (CommitOpen [F] F AC)
specialSoundProtocol = FiatShamir $ CommitOpen testCircuit

initAccumulator ::
    ( AdditiveMonoid f
    , AdditiveMonoid pi
    , AdditiveMonoid c
    ) => Accumulator pi f c m
initAccumulator = Accumulator (AccumulatorInstance zero [zero] [] zero zero) []

testInstanceProofPair :: forall pi c m .
    ( pi ~ [F]
    , m ~ [F]
    , c ~ F
    , RandomOracle c F
    , HomomorphicCommit m c
    ) => InstanceProofPair pi c m
testInstanceProofPair = instanceProof @_ @F specialSoundProtocol zero

specAccumulatorScheme :: IO ()
specAccumulatorScheme = pure ()

specProtostar :: IO ()
specProtostar = do
    specAccumulatorScheme