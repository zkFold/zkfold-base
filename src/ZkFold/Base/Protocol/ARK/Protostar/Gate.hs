module ZkFold.Base.Protocol.ARK.Protostar.Gate where

import           Data.Functor.Rep
import           Numeric.Natural                                 (Natural)
import           Prelude                                         hiding (Num (..), sum, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Algebra.Basic.Number                (KnownNat)
import           ZkFold.Base.Algebra.Polynomials.Multivariate    (Polynomial', evalVectorPolynomial, subs, var)
import           ZkFold.Base.Data.Matrix                         (Matrix, outer, sum1, transpose)
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.Internal     (PolynomialProtostar)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol (..), SpecialSoundTranscript)
import           ZkFold.Symbolic.Compiler.Arithmetizable         (Arithmetic)

data ProtostarGate (m :: Natural) (n :: Natural) (c :: Natural) (d :: Natural)

instance (Arithmetic f, KnownNat m, KnownNat n, KnownNat c) => SpecialSoundProtocol f (ProtostarGate m n c d) where
    type Witness f (ProtostarGate m n c d)       = Vector n (Vector c f)
    -- ^ [(a_j, w_j)]_{j=1}^n where [w_j]_{j=1}^n is from the paper together and [a_j]_{j=1}^n are their absolute indices
    type Input f (ProtostarGate m n c d)         = (Matrix (Vector m) (Vector n) f, Vector m (PolynomialProtostar f c d))
    -- ^ [s_{i, j}] and [G_i]_{i=1}^m in the paper
    type ProverMessage t (ProtostarGate m n c d)  = Vector n (Vector c t)
    -- ^ same as Witness
    type VerifierMessage t (ProtostarGate m n c d) = ()

    type Dimension (ProtostarGate m n c d)        = n
    type Degree (ProtostarGate m n c d)           = d

    rounds :: ProtostarGate m n c d -> Natural
    rounds _ = 1

    prover :: ProtostarGate m n c d
          -> Witness f (ProtostarGate m n c d)
          -> Input f (ProtostarGate m n c d)
          -> SpecialSoundTranscript f (ProtostarGate m n c d)
          -> ProverMessage f (ProtostarGate m n c d)
    prover _ w _ _ = w

    verifier' :: ProtostarGate m n c d
              -> Input f (ProtostarGate m n c d)
              -> SpecialSoundTranscript Natural (ProtostarGate m n c d)
              -> Vector (Dimension (ProtostarGate m n c d)) (Polynomial' f)
    verifier' _ (s, g) [(w, _)] =
      let w' = fmap ((var .) . subs) w :: Vector n (Zp c -> Polynomial' f)
          z  = transpose $ outer evalVectorPolynomial w' g
      in sum1 (mzipWithRep scale s z)
    verifier' _ _ _ = error "Invalid transcript"

    verifier :: ProtostarGate m n c d
             -> Input f (ProtostarGate m n c d)
             -> SpecialSoundTranscript f (ProtostarGate m n c d)
             -> Bool
    verifier _ (s, g) [(w, _)] =
      let w' = fmap subs w :: Vector n (Zp c -> f)
          z  = transpose $ outer evalVectorPolynomial w' g
      in all (== zero) $ sum1 $ mzipWithRep (*) s z
    verifier _ _ _ = error "Invalid transcript"

