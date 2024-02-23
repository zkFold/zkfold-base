module ZkFold.Base.Protocol.ARK.Protostar.Gate where

import           Data.ByteString                              (ByteString)
import           Data.Kind                                    (Type)
import           Prelude                                      hiding (Num (..), (^), (!!))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (evalPolynomial', subs)
import           ZkFold.Base.Data.Matrix                      (Matrix (..), outer, transpose, matrixDotProduct)
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.Internal  (PolynomialProtostar)
import           ZkFold.Base.Protocol.NonInteractiveProof     (NonInteractiveProof (..))

data ProtostarGate (m :: Type) (n :: Type) (c :: Type) (d :: Type) (f :: Type)

instance (Finite m, Finite n, Finite c, Eq f, FiniteField f) => NonInteractiveProof (ProtostarGate m n c d f) where
    type Transcript (ProtostarGate m n c d f)   = ByteString
    type Params (ProtostarGate m n c d f)       = (Matrix m n f, Vector m (PolynomialProtostar f c d))
    -- ^ (s_{i, j}, [G_i]_{i=1}^m) in the paper
    type SetupSecret (ProtostarGate m n c d f)  = ()
    type Setup (ProtostarGate m n c d f)        = (Matrix m n f, Vector m (PolynomialProtostar f c d))
    -- ^ same as Params
    type Witness (ProtostarGate m n c d f)      = Vector n (Vector c f)
    -- ^ [w_j]_{j=1}^n in the paper
    type ProverSecret (ProtostarGate m n c d f) = ()
    type Input (ProtostarGate m n c d f)        = ()
    type Proof (ProtostarGate m n c d f)        = Vector n (Vector c f)
    -- ^ same as Witness

    setup :: Params (ProtostarGate m n c d f) -> SetupSecret (ProtostarGate m n c d f) -> Setup (ProtostarGate m n c d f)
    setup p _ = p

    prove :: Setup (ProtostarGate m n c d f)
          -> Witness (ProtostarGate m n c d f)
          -> ProverSecret (ProtostarGate m n c d f)
          -> (Input (ProtostarGate m n c d f), Proof (ProtostarGate m n c d f))
    prove _ w _ = ((), w)

    verify :: Setup (ProtostarGate m n c d f) -> Input (ProtostarGate m n c d f) -> Proof (ProtostarGate m n c d f) -> Bool
    verify (s, g) _ w =
      let w' = fmap subs w :: Vector n (Zp c -> f)
          z  = transpose $ outer evalPolynomial' w' g
      in matrixDotProduct s z == zero