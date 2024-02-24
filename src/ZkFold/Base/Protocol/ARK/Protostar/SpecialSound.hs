{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.ARK.Protostar.SpecialSound where

import           Prelude        hiding (length)
import           System.Random  (Random)

type SpecialSoundTranscript a = [(ProverMessage a, VerifierMessage a)]

class Random (VerifierMessage a) => SpecialSoundProtocol a where
      type Setup a
      type Witness a
      type Input a
      type ProverMessage a
      type VerifierMessage a

      rounds :: Integer

      setup :: a -> Setup a

      prover :: Setup a -> Witness a -> Input a -> SpecialSoundTranscript a -> ProverMessage a

      challenge :: Setup a -> Input a -> Integer -> VerifierMessage a

      verifier :: Setup a -> Input a -> SpecialSoundTranscript a -> Bool

runSpecialSoundProtocol :: forall a . SpecialSoundProtocol a => Setup a -> Witness a -> Input a -> Integer -> SpecialSoundTranscript a
runSpecialSoundProtocol s w i r =
      let f ts j = (prover @a s w i ts, challenge @a s i j) : ts
      in foldl f [] [1 .. min r (rounds @a)]