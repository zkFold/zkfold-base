{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans     #-}

module Tests.Blake2b where

import           Crypto.Hash.BLAKE2.BLAKE2b                  (hash)
import qualified Data.ByteString                             as B
import qualified Data.ByteString.Internal                    as BI
import qualified Data.Vector                                 as V
import qualified GHC.Num                                     as GHC
import           Numeric.Natural                             (Natural)
import           Prelude                                     (Eq (..), Foldable (..), Functor (..), IO,
                                                              Monoid (..), fromIntegral, replicate, undefined, ($),
                                                              (<$>))
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Class             (AdditiveMonoid, AdditiveSemigroup (..), Finite,
                                                              FromConstant (..), MultiplicativeMonoid, ToConstant)
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b     (Blake2bByteString, andUInt, blake2b, blake2b_256,
                                                              blake2b_final, blake2b_init, blake2b_update, shiftUIntR)
import           ZkFold.Symbolic.Data.Bool                   (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString             (ByteString, Concat, ShiftBits (..), ToWords)
import           ZkFold.Symbolic.Data.Combinators            (Iso)
import           ZkFold.Symbolic.Data.UInt                   (UInt, toConstant)

{-

   This module computes a series of keyed and unkeyed hashes from
   deterministically generated pseudorandom data and computes a hash
   over those results.  This is a fairly exhaustive, yet compact and
   fast method for verifying that the hashing module is functioning
   correctly.

   Such testing is RECOMMENDED, especially when compiling the
   implementation for a new a target platform configuration.
   Furthermore, some security standards, such as FIPS-140, may require a
   Power-On Self Test (POST) to be performed every time the
   cryptographic module is loaded [FIPS140-2IG].

-}

-- Deterministic sequences (Fibonacci generator).
selftestSeq ::
    ( AdditiveSemigroup (UInt 8 b a)
    , ShiftBits (ByteString 8 b a)
    , BoolType (ByteString 8 b a)
    , Iso (UInt 8 b a) (ByteString 8 b a)
    , FromConstant Natural (UInt 8 b a) ) =>
    V.Vector (UInt 8 b a) -> Natural -> Natural -> V.Vector (UInt 8 b a)
selftestSeq out len seed =
    let a' = fromConstant $ 0xDEAD4BAD GHC.* seed -- prime
        b' = fromConstant @Natural 1

        indexs = [0..fromIntegral len GHC.-1]

        for' i (o, a, b) = (o V.// [(i, ((a + b) `shiftUIntR` 24) `andUInt` fromConstant @Natural 0xFF)], b, a + b)

    in (\(out', _, _) -> out') $ foldr for' (out, a', b') indexs -- fill the buf

-- BLAKE2b self-test validation. Return 0 when OK.
blake2bSelftest :: forall a b .
    ( Blake2bByteString b a
    , ToConstant (UInt 8 b a) Natural
    , MultiplicativeMonoid (UInt 64 b a)
    , Finite a
    , AdditiveMonoid a
    , FromConstant GHC.Integer (UInt 64 b a)
    , Iso (UInt 8 b a) (ByteString 8 b a)
    , AdditiveSemigroup (UInt 8 b a), ShiftBits (ByteString 8 b a), BoolType (ByteString 8 b a) ) => Spec
blake2bSelftest =
    let -- grand hash of hash results
        blake2b_res = V.fromList $ fromConstant @Natural @(UInt 8 b a) <$> [
           0xC2, 0x3A, 0x78, 0x00, 0xD9, 0x81, 0x23, 0xBD,
           0x10, 0xF5, 0x06, 0xC6, 0x1E, 0x29, 0xDA, 0x56,
           0x03, 0xD7, 0x63, 0xB8, 0xBB, 0xAD, 0x2E, 0x73,
           0x7F, 0x5E, 0x76, 0x5A, 0x7B, 0xCC, 0xD4, 0x75]

        -- parameter sets
        b2b_md_len = V.fromList @Natural $ [20, 32, 48, 64]
        b2b_in_len = V.fromList @Natural $ [0, 3, 128, 129, 255, 1024]

        -- 256-bit hash for testing
        init = blake2b_init 32 mempty 0

        zeroVec = V.fromList $ replicate 1024 (fromConstant @Natural 0)

        roundOut outlen state =
            let foo inlen (ctx', in', md', key') =
                    let in''  = selftestSeq in' inlen inlen -- unkeyed has
                        md''  = blake2b md' outlen mempty 0 in' inlen
                        ctx'' = blake2b_update ctx' md'' outlen -- hash the hash

                        key''  = selftestSeq key' outlen outlen -- keyed hash
                        md'''  = blake2b md'' outlen key'' outlen in'' inlen
                        ctx''' = blake2b_update ctx'' md''' outlen -- hash the hash
                    in (ctx''', in'', md''', key'')
            in foldr foo state b2b_in_len

        (ctx, _, md, _) = foldr roundOut (init, V.take 1024 zeroVec, V.take 64 zeroVec, V.take 64 zeroVec) b2b_md_len

        -- compute and compare the hash of hashes
        final = blake2b_final ctx md

        a = fmap (toConstant @_ @Natural) blake2b_res

        b = fmap (toConstant @(UInt 8 b a) @Natural) (V.take 32 final)

    in it "compare hash results with symbolic blake2b " $ a == b


instance ToConstant (ByteString n b a) B.ByteString where
    toConstant _ = undefined

blake2bSimple :: forall a b .
    ( Blake2bByteString b a
    , Iso (UInt 8 b a) (ByteString 8 b a)
    , FromConstant Natural (ByteString 8 b a)
    , Concat (ByteString 8 b a) (ByteString 8 b a)
    , ToWords (ByteString 8 b a) (ByteString 8 b a)
    , Concat (ByteString 8 b a) (ByteString 256 b a)) => Spec
blake2bSimple =
    let bs = ""
        a = blake2b_256 $ fromConstant @B.ByteString @(ByteString 8 b a) bs
        b = hash 32 BI.empty bs
    in  it "simple test with cardano-crypto " $ b == toConstant a

specBlake2b :: IO ()
specBlake2b = hspec $ describe "BLAKE2b self-test validation" $ do
  blake2bSimple @(Zp BLS12_381_Scalar) @Vector
  blake2bSelftest @(Zp BLS12_381_Scalar) @Vector
