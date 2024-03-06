module ZkFold.Base.Protocol.ARK.Protostar.Permutation where

import           Data.Kind                                       (Type)
import           Data.Zip                                        (Zip(..))
import           Prelude                                         hiding (Num (..), (^), (!!), zipWith)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                (N1)
import           ZkFold.Base.Algebra.Basic.Permutations          (Permutation, applyPermutation)
import           ZkFold.Base.Algebra.Polynomials.Multivariate    (SomePolynomial, var)
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)
import           ZkFold.Symbolic.Compiler                        (Arithmetic)

data ProtostarPermutation (n :: Type)

instance Arithmetic f => SpecialSoundProtocol f (ProtostarPermutation n) where
    type Witness f (ProtostarPermutation n)         = Vector n f
    -- ^ w in the paper
    type Input f (ProtostarPermutation n)           = Permutation n
    -- ^ \sigma in the paper
    type ProverMessage t (ProtostarPermutation n)   = Vector n t
    -- ^ same as Witness
    type VerifierMessage t (ProtostarPermutation n) = ()

    type Dimension (ProtostarPermutation n)         = n
    type Degree (ProtostarPermutation n)            = N1

    rounds :: ProtostarPermutation n -> Integer
    rounds _ = 1

    prover :: ProtostarPermutation n
           -> Witness f (ProtostarPermutation n)
           -> Input f (ProtostarPermutation n)
           -> SpecialSoundTranscript f (ProtostarPermutation n)
           -> ProverMessage f (ProtostarPermutation n)
    prover _ w _ _ = w

    verifier' :: ProtostarPermutation n
              -> Input f (ProtostarPermutation n)
              -> SpecialSoundTranscript Integer (ProtostarPermutation n)
              -> Vector (Dimension (ProtostarPermutation n)) (SomePolynomial f)
    verifier' _ sigma [(w, _)] = zipWith (-) (applyPermutation sigma wX) wX
      where wX = fmap var w
    verifier' _ _ _ = error "Invalid transcript"


    verifier :: ProtostarPermutation n
             -> Input f (ProtostarPermutation n)
             -> SpecialSoundTranscript f (ProtostarPermutation n)
             -> Bool
    verifier _ sigma [(w, _)] = applyPermutation sigma w == w
    verifier _ _     _        = error "Invalid transcript"