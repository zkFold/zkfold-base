module ZkFold.Base.Protocol.ARK.Protostar.Permutation where

import           Data.ByteString                              (ByteString)
import           Data.Kind                                    (Type)
import           Data.Typeable                                (Typeable)
import           Prelude                                      hiding (Num (..), (^), (!!))
import           Test.QuickCheck                              (Arbitrary)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Permutations       (Permutation, applyPermutation)
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Base.Protocol.NonInteractiveProof     (NonInteractiveProof (..))

data ProtostarPermutation (n :: Type) (f :: Type)

instance (Finite n, Typeable n, Typeable f, Show f, Arbitrary f, Eq f)
        => NonInteractiveProof (ProtostarPermutation n f) where
    type Transcript (ProtostarPermutation n f)   = ByteString
    type Params (ProtostarPermutation n f)       = Permutation n
    -- ^ \sigma in the paper
    type SetupSecret (ProtostarPermutation n f)  = ()
    type Setup (ProtostarPermutation n f)        = Permutation n
    -- ^ same as Params
    type ProverSecret (ProtostarPermutation n f) = ()
    type Witness (ProtostarPermutation n f)      = Vector n f
    -- ^ w in the paper
    type Input (ProtostarPermutation n f)        = ()
    type Proof (ProtostarPermutation n f)        = Vector n f
    -- ^ same as Witness

    setup :: Params (ProtostarPermutation n f) -> SetupSecret (ProtostarPermutation n f) -> Setup (ProtostarPermutation n f)
    setup p _ = p

    prove :: ProverSecret (ProtostarPermutation n f)
          -> Setup (ProtostarPermutation n f)
          -> Witness (ProtostarPermutation n f)
          -> (Input (ProtostarPermutation n f), Proof (ProtostarPermutation n f))
    prove _ _ w = ((), w)

    verify :: Setup (ProtostarPermutation n f) -> Input (ProtostarPermutation n f) -> Proof (ProtostarPermutation n f) -> Bool
    verify sigma _ w = applyPermutation sigma w == w