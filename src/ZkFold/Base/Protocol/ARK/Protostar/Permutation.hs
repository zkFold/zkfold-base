module ZkFold.Base.Protocol.ARK.Protostar.Permutation where

import           Data.Zip                                        (Zip (..))
import           Numeric.Natural                                 (Natural)
import           Prelude                                         hiding (Num (..), zipWith, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Permutations          (Permutation, applyPermutation)
import           ZkFold.Base.Algebra.Polynomials.Multivariate    (var)
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (LMap, SpecialSoundProtocol (..),
                                                                  SpecialSoundTranscript)
import           ZkFold.Symbolic.Compiler                        (Arithmetic)

data ProtostarPermutation (n :: Natural)

instance Arithmetic f => SpecialSoundProtocol f (ProtostarPermutation n) where
    type Witness f (ProtostarPermutation n)         = Vector n f
    -- ^ w in the paper
    type Input f (ProtostarPermutation n)           = Permutation n
    -- ^ \sigma in the paper
    type ProverMessage t (ProtostarPermutation n)   = Vector n t
    -- ^ same as Witness
    type VerifierMessage t (ProtostarPermutation n) = ()

    type Dimension (ProtostarPermutation n)         = n
    type Degree (ProtostarPermutation n)            = 1

    rounds :: ProtostarPermutation n -> Natural
    rounds _ = 1

    prover :: ProtostarPermutation n
           -> Witness f (ProtostarPermutation n)
           -> Input f (ProtostarPermutation n)
           -> SpecialSoundTranscript f (ProtostarPermutation n)
           -> ProverMessage f (ProtostarPermutation n)
    prover _ w _ _ = w

    algebraicMap :: ProtostarPermutation n
                 -> Input f (ProtostarPermutation n)
                 -> [ProverMessage Natural (ProtostarPermutation n)]
                 -> [VerifierMessage Natural (ProtostarPermutation n)]
                 -> LMap (Dimension (ProtostarPermutation n)) f
    algebraicMap _ sigma [w] _ = zipWith (-) (applyPermutation sigma wX) wX
      where wX = fmap var w
    algebraicMap _ _ _ _ = error "Invalid transcript"


    verifier :: ProtostarPermutation n
             -> Input f (ProtostarPermutation n)
             -> [ProverMessage f (ProtostarPermutation n)]
             -> [VerifierMessage f (ProtostarPermutation n)]
             -> Bool
    verifier _ sigma [w] _ = applyPermutation sigma w == w
    verifier _ _     _   _ = error "Invalid transcript"
