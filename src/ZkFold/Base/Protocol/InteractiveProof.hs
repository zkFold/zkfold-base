{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.InteractiveProof where

import           Prelude

data TranscriptProver a   = TranscriptProver (ProverMessage a) (TranscriptVerifier a)
data TranscriptVerifier a = TranscriptEmpty | TranscriptVerifier (VerifierMessage a) (TranscriptProver a)

class InteractiveProof a where
    type Params a

    type SetupSecret a

    type Setup a

    type Witness a

    type ProverSecret a

    type Input a

    type ProverMessage a

    type VerifierSecret a

    type VerifierMessage a

    setup :: Params a -> SetupSecret a -> Setup a

    instantiate :: Setup a -> Witness a -> Input a

    prove :: Setup a
          -> Witness a
          -> Input a
          -> Maybe (VerifierMessage a, TranscriptProver a)
          -> ProverSecret a
          -> (ProverMessage a, TranscriptProver a)

    verify :: Setup a
           -> Input a
           -> (ProverMessage a, TranscriptVerifier a)
           -> VerifierSecret a
           -> (VerifierMessage a, TranscriptVerifier a)