module ZkFold.Base.Protocol.ARK.Protostar.Permutation where

import           Data.Kind                                       (Type)
import           Prelude                                         hiding (Num (..), (^), (!!))

import           ZkFold.Base.Algebra.Basic.Permutations          (Permutation, applyPermutation)
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)

data ProtostarPermutation (n :: Type) (f :: Type)

instance Eq f => SpecialSoundProtocol (ProtostarPermutation n f) where
    type Witness (ProtostarPermutation n f)         = Vector n f
    -- ^ w in the paper
    type Input (ProtostarPermutation n f)           = Permutation n
    -- ^ \sigma in the paper
    type ProverMessage (ProtostarPermutation n f)   = Vector n f
    -- ^ same as Witness
    type VerifierMessage (ProtostarPermutation n f) = ()

    rounds :: Integer
    rounds = 1

    prover :: ProtostarPermutation n f
          -> Witness (ProtostarPermutation n f)
          -> Input (ProtostarPermutation n f)
          -> SpecialSoundTranscript (ProtostarPermutation n f)
          -> ProverMessage (ProtostarPermutation n f)
    prover _ w _ _ = w

    verifier :: ProtostarPermutation n f
             -> Input (ProtostarPermutation n f)
             -> SpecialSoundTranscript (ProtostarPermutation n f)
             -> Bool
    verifier _ sigma [(w, _)] = applyPermutation sigma w == w
    verifier _ _     _        = error "Invalid transcript"