module ZkFold.Base.Protocol.ARK.Protostar.Gate where

import           Data.ByteString                              (ByteString)
import           Data.Kind                                    (Type)
import           Data.Typeable                                (Typeable)
import           Prelude                                      (Show, Eq, Bool, undefined)
import           Test.QuickCheck                              (Arbitrary)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Polynomial)
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Base.Protocol.NonInteractiveProof     (NonInteractiveProof (..))

data ProtostarGate (m :: Type) (n :: Type) (c :: Type) (d :: Type) (f :: Type)

-- TODO: constrain arity and degree of the gates
instance (Finite m, Finite n, Finite c, Finite d, Typeable m, Typeable n, Typeable c, Typeable d, Typeable f,
        Show f, Arbitrary f, FiniteField f, Eq f) => NonInteractiveProof (ProtostarGate m n c d f) where
    type Transcript (ProtostarGate m n c d f)   = ByteString
    type Params (ProtostarGate m n c d f)       = Vector m (Vector n f, Polynomial f)
    type SetupSecret (ProtostarGate m n c d f)  = ()
    type Setup (ProtostarGate m n c d f)        = Vector m (Vector n f, Polynomial f)
    type ProverSecret (ProtostarGate m n c d f) = ()
    type Witness (ProtostarGate m n c d f)      = Vector n (Vector c f)
    type Input (ProtostarGate m n c d f)        = ()
    type Proof (ProtostarGate m n c d f)        = ()

    setup :: Params (ProtostarGate m n c d f) -> SetupSecret (ProtostarGate m n c d f) -> Setup (ProtostarGate m n c d f)
    setup = undefined

    prove :: ProverSecret (ProtostarGate m n c d f)
          -> Setup (ProtostarGate m n c d f)
          -> Witness (ProtostarGate m n c d f)
          -> (Input (ProtostarGate m n c d f), Proof (ProtostarGate m n c d f))
    prove = undefined

    verify :: Setup (ProtostarGate m n c d f) -> Input (ProtostarGate m n c d f) -> Proof (ProtostarGate m n c d f) -> Bool
    verify = undefined