{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.NonInteractiveProof.Internal where

import           Crypto.Hash.BLAKE2.BLAKE2b                 (hash)
import           Data.ByteString                            (ByteString)
import           Data.Maybe                                 (fromJust)
import qualified Data.Vector                                as V
import           Data.Word                                  (Word8)
import           Numeric.Natural                            (Natural)
import           Prelude                                    hiding (Num ((*)), sum)

import           ZkFold.Base.Algebra.Basic.Class            (MultiplicativeSemigroup ((*)), scale, sum)
import           ZkFold.Base.Algebra.EllipticCurve.Class    (SubgroupCurve (..))
import           ZkFold.Base.Algebra.Polynomials.Univariate (Poly, PolyVec, fromPolyVec)
import           ZkFold.Base.Data.ByteString

class Monoid ts => ToTranscript ts a where
    toTranscript :: a -> ts

instance Binary a => ToTranscript ByteString a where
    toTranscript = toByteString

transcript :: ToTranscript ts a => ts -> a -> ts
transcript ts a = ts <> toTranscript a

class Monoid ts => FromTranscript ts a where
    fromTranscript :: ts -> a

instance Binary a => FromTranscript ByteString a where
    fromTranscript = fromJust . fromByteString . hash 28 mempty

challenge :: forall ts a . FromTranscript ts a => ts -> a
challenge = fromTranscript

challenges :: (ToTranscript ts Word8, FromTranscript ts a) => ts -> Natural -> ([a], ts)
challenges ts0 n = go ts0 n []
  where
    go ts 0 acc = (acc, ts)
    go ts k acc =
        let c   = challenge ts
            ts' = ts `transcript` (0 :: Word8)
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

class SubgroupCurve curve Bool baseField scalarField point
  => CoreFunction curve baseField scalarField point core where
    msm :: V.Vector (point baseField) -> PolyVec scalarField size -> point baseField

    polyMul :: Poly scalarField -> Poly scalarField -> Poly scalarField

data HaskellCore

instance (Eq scalarField, SubgroupCurve curve Bool baseField scalarField point)
  => CoreFunction curve baseField scalarField point HaskellCore where
    msm gs f = sum $ V.zipWith scale (fromPolyVec f) gs
    polyMul = (*)
