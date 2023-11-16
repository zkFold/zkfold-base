{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Prelude (Bool)

class NonInteractiveProof a where
    type Params a

    type SetupSecret a

    type Setup a

    type ProverSecret a

    type Witness a

    type Input a

    type Proof a

    setup :: Params a -> SetupSecret a -> Setup a

    prove :: ProverSecret a -> Setup a -> Witness a -> (Input a, Proof a)

    verify :: Setup a -> Input a -> Proof a -> Bool