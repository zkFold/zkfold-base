module ZkFold.Base.Protocol.Protostar.Permutation where

import           Prelude                                     hiding (Num (..), zipWith, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Permutations      (Permutation, applyPermutation)
import           ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Protocol.Protostar.SpecialSound (AlgebraicMap (..), SpecialSoundProtocol (..),
                                                              SpecialSoundTranscript)
import           ZkFold.Symbolic.Class                       (Arithmetic)

data ProtostarPermutation (n :: Natural)

instance (Arithmetic f, KnownNat n) => SpecialSoundProtocol f (ProtostarPermutation n) where
    type Witness f (ProtostarPermutation n)         = Vector n f
    -- ^ w in the paper
    type Input f (ProtostarPermutation n)           = Permutation n
    -- ^ \sigma in the paper
    type ProverMessage f (ProtostarPermutation n)   = Vector n f
    -- ^ same as Witness
    type VerifierMessage f (ProtostarPermutation n) = ()
    type VerifierOutput f (ProtostarPermutation n)  = Bool

    type Degree (ProtostarPermutation n)            = 1

    outputLength _ = value @n

    rounds :: ProtostarPermutation n -> Natural
    rounds _ = 1

    prover :: ProtostarPermutation n
           -> Witness f (ProtostarPermutation n)
           -> Input f (ProtostarPermutation n)
           -> SpecialSoundTranscript f (ProtostarPermutation n)
           -> ProverMessage f (ProtostarPermutation n)
    prover _ w _ _ = w

    verifier :: ProtostarPermutation n
             -> Input f (ProtostarPermutation n)
             -> [ProverMessage f (ProtostarPermutation n)]
             -> [f]
             -> Bool
    verifier p sigma [w] ts = algebraicMap p sigma [w] ts one == V.fromVector w
    verifier _ _     _   _  = error "Invalid transcript"

instance (Arithmetic f, KnownNat n) => AlgebraicMap f (ProtostarPermutation n) where
    type MapInput f (ProtostarPermutation n) = Permutation n
    type MapMessage f (ProtostarPermutation n) = Vector n f

    algebraicMap :: ProtostarPermutation n
                 -> MapInput f (ProtostarPermutation n)
                 -> [MapMessage f (ProtostarPermutation n)]
                 -> [f]
                 -> f
                 -> [f]
    algebraicMap _ sigma [w] _ _ = V.fromVector $ applyPermutation sigma w
    algebraicMap _ _ _ _ _       = error "Invalid transcript"


