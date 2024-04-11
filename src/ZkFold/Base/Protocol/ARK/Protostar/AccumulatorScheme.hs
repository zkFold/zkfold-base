{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme where

import           Prelude                                         hiding (length)

import           ZkFold.Base.Protocol.ARK.Protostar.Accumulator
import           ZkFold.Base.Protocol.ARK.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.ARK.Protostar.FiatShamir   (FiatShamir (..))
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (Input, ProverMessage)

class AccumulatorScheme f c m a where
  commit :: a -> m -> c

  prover :: a -> Accumulator f c m -> Accumulator f c m -> (Accumulator f c m, [f])

  verifier ::
    a ->
    AccumulatorInstance f c ->
    AccumulatorInstance f c ->
    (AccumulatorInstance f c, [f]) ->
    Bool

  decider :: a -> Accumulator f c m -> Bool

instance (Input f a ~ f, ProverMessage f a ~ m) => AccumulatorScheme f c m (FiatShamir f (CommitOpen f c a)) where
  commit (FiatShamir (CommitOpen cm _) _) = cm

  prover = undefined

  verifier = undefined

  decider = undefined
