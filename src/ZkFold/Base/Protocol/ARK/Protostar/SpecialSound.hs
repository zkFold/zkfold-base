{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.ARK.Protostar.SpecialSound where

import           Prelude        hiding (length)

type SpecialSoundTranscript a = [(ProverMessage a, VerifierMessage a)]

class SpecialSoundProtocol a where
      type Witness a
      type Input a
      type ProverMessage a
      type VerifierMessage a

      rounds :: Integer

      prover :: a -> Witness a -> Input a -> SpecialSoundTranscript a -> ProverMessage a

      verifier :: a -> Input a -> SpecialSoundTranscript a -> Bool

runSpecialSoundProtocol :: forall a . SpecialSoundProtocol a => a
      -> Witness a
      -> Input a
      -> (SpecialSoundTranscript a -> VerifierMessage a)
      -> SpecialSoundTranscript a
runSpecialSoundProtocol a w i challenge =
      let f ts _  = (prover a w i ts, challenge ts) : ts
      in foldl f [] [1 .. rounds @a]