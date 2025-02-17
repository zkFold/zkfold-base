{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.FiatShamir where

import           Data.Constraint                     (withDict)
import           Data.Constraint.Nat                 (plusMinusInverse1)
import           Prelude                             hiding (Bool (..), Eq (..), init, length, pi, scanl, unzip)

import           ZkFold.Base.Algebra.Basic.Class     (Ring)
import           ZkFold.Base.Algebra.Basic.Number    (KnownNat, type (-))
import           ZkFold.Base.Data.Vector             (Vector, init, scanl, unfold)
import           ZkFold.Base.Protocol.IVC.Commit     (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.Oracle     (HashAlgorithm, oracle)
import           ZkFold.Base.Protocol.IVC.Predicate  (PredicateFunctionAssumptions)
import           ZkFold.Symbolic.MonadCircuit        (ResidueField)

data FiatShamir k a i p c = FiatShamir
    {
        input :: forall f . PredicateFunctionAssumptions a f
            => i f
            -> p f
            -> i f

      , prover  :: forall f . (PredicateFunctionAssumptions a f, ResidueField f, HomomorphicCommit [f] (c f))
            => i f
            -> p f
            -> Vector k ([f], c f)

      , verifier :: forall f . (PredicateFunctionAssumptions a f, HomomorphicCommit [f] (c f))
            => i f
            -> Vector k ([f], c f)
            -> ([f], Vector k (c f))
    }

-- The transcript of the Fiat-Shamired protocol (ignoring the last round)
transcript :: forall algo k c f .
    ( HashAlgorithm algo
    , Ring f
    , Foldable c
    ) => f -> Vector k (c f) -> Vector (k-1) f
transcript r0 cs = withDict (plusMinusInverse1 @1 @k) $ init $ init $ scanl (curry (oracle @algo)) r0 cs

fiatShamir :: forall algo k a i p c .
    ( HashAlgorithm algo
    , KnownNat k
    , Foldable i
    , Foldable c
    ) => CommitOpen k a i p c -> FiatShamir k a i p c
fiatShamir CommitOpen {..} =
    let
        prover' :: forall f . (PredicateFunctionAssumptions a f, ResidueField f, HomomorphicCommit [f] (c f))
            => i f
            -> p f
            -> Vector k ([f], c f)
        prover' pi0 w =
            let r0 = oracle @algo pi0
                f (r, k) =
                    let (m', c') = prover pi0 w r k
                    in ((m', c'), (oracle @algo (r, c'), k + 1))
            in unfold f (r0, 1)

        verifier' :: forall f . (PredicateFunctionAssumptions a f, HomomorphicCommit [f] (c f))
            => i f
            -> Vector k ([f], c f)
            -> ([f], Vector k (c f))
        verifier' pi pms =
            let r0 = oracle @algo pi
                rs = transcript @algo r0 $ fmap snd pms
            in verifier pi pms rs
    in
        FiatShamir input prover' verifier'
