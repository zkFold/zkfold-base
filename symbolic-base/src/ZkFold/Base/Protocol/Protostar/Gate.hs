module ZkFold.Base.Protocol.Protostar.Gate where

import           Data.Zip                                     (zipWith)
import           GHC.Generics
import           Numeric.Natural                              (Natural)
import           Prelude                                      hiding (Num (..), zipWith, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Algebra.Basic.Number             (KnownNat, value)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (evalMonomial, evalPolynomial, subs)
import           ZkFold.Base.Data.Matrix                      (Matrix (..), outer, sum1, transpose)
import qualified ZkFold.Base.Data.Vector                      as V
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Base.Protocol.Protostar.Internal      (PolynomialProtostar (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound  (AlgebraicMap (..), SpecialSoundProtocol (..),
                                                               SpecialSoundTranscript)
import           ZkFold.Symbolic.Class                        (Arithmetic)

data ProtostarGate (m :: Natural) (n :: Natural) (c :: Natural) (d :: Natural)
    deriving Generic

instance (Arithmetic f, KnownNat m, KnownNat n) => SpecialSoundProtocol f (ProtostarGate m n c d) where
    type Witness f (ProtostarGate m n c d)       = Vector n (Vector c f)
    -- ^ [(a_j, w_j)]_{j=1}^n where [w_j]_{j=1}^n is from the paper together and [a_j]_{j=1}^n are their absolute indices
    type Input f (ProtostarGate m n c d)         = (Matrix m n f, Vector m (PolynomialProtostar f c d))
    -- ^ [s_{i, j}] and [G_i]_{i=1}^m in the paper
    type ProverMessage f (ProtostarGate m n c d)  = Vector n (Vector c f)
    -- ^ same as Witness
    type VerifierMessage f (ProtostarGate m n c d) = ()
    type VerifierOutput f (ProtostarGate m n c d)  = Bool

    type Degree (ProtostarGate m n c d)           = d

    outputLength _ = value @n

    rounds :: ProtostarGate m n c d -> Natural
    rounds _ = 1

    prover :: ProtostarGate m n c d
          -> Witness f (ProtostarGate m n c d)
          -> Input f (ProtostarGate m n c d)
          -> SpecialSoundTranscript f (ProtostarGate m n c d)
          -> ProverMessage f (ProtostarGate m n c d)
    prover _ w _ _ = w

    verifier :: ProtostarGate m n c d
             -> Input f (ProtostarGate m n c d)
             -> [ProverMessage f (ProtostarGate m n c d)]
             -> [f]
             -> Bool
    verifier gate (s, g) [w] ts = all (== zero) $ algebraicMap gate (s, g) [w] ts one
    verifier _ _ _ _            = error "Invalid transcript"

instance (Arithmetic f, KnownNat m, KnownNat n) => AlgebraicMap f (ProtostarGate m n c d) where
    type MapInput f (ProtostarGate m n c d)    = (Matrix m n f, Vector m (PolynomialProtostar f c d))
    type MapMessage f (ProtostarGate m n c d)  = Vector n (Vector c f)

    algebraicMap :: ProtostarGate m n c d
                 -> MapInput f (ProtostarGate m n c d)
                 -> [MapMessage f (ProtostarGate m n c d)]
                 -> [f]
                 -> f
                 -> [f]
    algebraicMap _ (s, g) [w] _ _ =
      let w' = fmap subs w :: Vector n (Zp c -> f)
          z  = transpose $ outer (evalPolynomial evalMonomial) w' $ fmap (\(PolynomialProtostar p) -> p) g
      in V.fromVector $ sum1 $ zipWith (*) s z
    algebraicMap _ _ _ _ _ = error "Invalid transcript"
