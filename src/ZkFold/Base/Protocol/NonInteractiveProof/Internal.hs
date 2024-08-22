{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.NonInteractiveProof.Internal where

import           Crypto.Hash.BLAKE2.BLAKE2b                 (hash)
import           Data.ByteString                            (ByteString, cons)
import           Data.Maybe                                 (fromJust)
import qualified Data.Vector                                as V
import           Numeric.Natural                            (Natural)
import           Prelude                                    hiding (sum)

import           ZkFold.Base.Algebra.Basic.Class            (sum)
import           ZkFold.Base.Algebra.EllipticCurve.Class    (EllipticCurve (..), Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec, fromPolyVec)
import           ZkFold.Base.Data.ByteString

class Monoid t => ToTranscript t a where
    toTranscript :: a -> t

instance Binary a => ToTranscript ByteString a where
    toTranscript = toByteString

transcript :: ToTranscript t a => t -> a -> t
transcript ts a = ts <> toTranscript a

class Monoid t => FromTranscript t a where
    newTranscript  :: t -> t
    fromTranscript :: t -> a

instance Binary a => FromTranscript ByteString a where
    newTranscript  = cons 0
    fromTranscript = fromJust . fromByteString . hash 28 mempty

challenge :: forall t a . FromTranscript t a => t -> (a, t)
challenge ts =
    let ts' = newTranscript @t @a ts
    in (fromTranscript ts', ts')

challenges :: FromTranscript t a => t -> Natural -> ([a], t)
challenges ts0 n = go ts0 n []
  where
    go ts 0 acc = (acc, ts)
    go ts k acc =
        let (c, ts') = challenge ts
        in go ts' (k - 1) (c : acc)

class NonInteractiveProof a core where
    type Transcript a

    type SetupProve a

    type SetupVerify a

    type Witness a

    type Input a

    type Proof a

    setupProve :: a -> SetupProve a

    setupVerify :: a -> SetupVerify a

    prove :: SetupProve a -> Witness a -> (Input a, Proof a)

    verify :: SetupVerify a -> Input a -> Proof a -> Bool

class (EllipticCurve curve) => CoreFunction curve core where
    msm :: (f ~ ScalarField curve) => V.Vector (Point curve) -> PolyVec f size -> Point curve

data HaskellCore

instance (EllipticCurve curve, f ~ ScalarField curve) => CoreFunction curve HaskellCore where
    msm gs f = sum $ V.zipWith mul (fromPolyVec f) gs
