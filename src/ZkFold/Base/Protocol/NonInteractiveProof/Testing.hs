{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.NonInteractiveProof.Testing where

import           Prelude

import           ZkFold.Base.Protocol.NonInteractiveProof.Internal

class (NonInteractiveProof a core, NonInteractiveProof b core) => CompatibleNonInteractiveProofs a b core where
    nipSetupTransform    :: SetupVerify a -> SetupVerify b
    nipInputTransform    :: Input a -> Input b
    nipProofTransform    :: Proof a -> Proof b

nipCompatibility :: forall a b core . CompatibleNonInteractiveProofs a b core
    => a -> Witness a -> Bool
nipCompatibility a w =
    let (i, p) = prove @a @core (setupProve @a @core a) w
        s'     = nipSetupTransform @a @b @core (setupVerify @a @core a)
        i'     = nipInputTransform @a @b @core i
        p'     = nipProofTransform @a @b @core p
    in verify @b @core s' i' p'

instance NonInteractiveProof a core => CompatibleNonInteractiveProofs a a core where
    nipSetupTransform    = id
    nipInputTransform    = id
    nipProofTransform    = id

data NonInteractiveProofTestData a core = (NonInteractiveProof a core) => TestData a (Witness a)

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a core) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w
