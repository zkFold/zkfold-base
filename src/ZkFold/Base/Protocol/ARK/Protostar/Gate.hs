module ZkFold.Base.Protocol.ARK.Protostar.Gate where

import           Data.Kind                                       (Type)
import           Prelude                                         hiding (Num (..), (^), (!!))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate    (evalPolynomial', subs)
import           ZkFold.Base.Data.Matrix                         (Matrix (..), outer, transpose, matrixDotProduct)
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.Internal     (PolynomialProtostar)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)

data ProtostarGate (m :: Type) (n :: Type) (c :: Type) (d :: Type) (f :: Type)     

instance (Finite m, Finite n, Finite c, Eq f, FiniteField f) => SpecialSoundProtocol (ProtostarGate m n c d f) where
    type Witness (ProtostarGate m n c d f)       = Vector n (Vector c f)
    -- ^ [w_j]_{j=1}^n in the paper
    type Input (ProtostarGate m n c d f)         = (Matrix m n f, Vector m (PolynomialProtostar f c d))
    -- ^ [s_{i, j}] and [G_i]_{i=1}^m in the paper
    type ProverMessage (ProtostarGate m n c d f) = Vector n (Vector c f)
    -- ^ same as Witness
    type VerifierMessage (ProtostarGate m n c d f) = ()

    rounds :: Integer
    rounds = 1

    prover :: ProtostarGate m n c d f
          -> Witness (ProtostarGate m n c d f)
          -> Input (ProtostarGate m n c d f)
          -> SpecialSoundTranscript (ProtostarGate m n c d f)
          -> ProverMessage (ProtostarGate m n c d f)
    prover _ w _ _ = w

    verifier :: ProtostarGate m n c d f
             -> Input (ProtostarGate m n c d f)
             -> SpecialSoundTranscript (ProtostarGate m n c d f)
             -> Bool
    verifier _ (s, g) [(w, _)] =
      let w' = fmap subs w :: Vector n (Zp c -> f)
          z  = transpose $ outer evalPolynomial' w' g
      in matrixDotProduct s z == zero
    verifier _ _ _ = error "Invalid transcript"