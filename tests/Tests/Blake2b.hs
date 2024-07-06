{-# LANGUAGE AllowAmbiguousTypes #-}

module Tests.Blake2b where

import           Crypto.Hash.BLAKE2.BLAKE2b                  (hash)
import qualified Data.ByteString.Internal                    as BI
import           Numeric.Natural                             (Natural)
import           Prelude                                     (Eq (..), IO, ($))
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString             (ByteString, Concat, ReverseEndianness, ShiftBits,
                                                              ToWords (..), Truncate (..))
import           ZkFold.Symbolic.Data.Combinators            (Extend)

-- TODO: We need a proper test for both numeric and symbolic blake2b hashing

blake2bSimple :: forall a b .
    ( Extend (ByteString 0 b a) (ByteString 1024 b a)
    , ShiftBits (ByteString 1024 b a)
    , ReverseEndianness 64 (ByteString 1024 b a)
    , ToWords (ByteString 1024 b a) (ByteString 64 b a)
    , Truncate (ByteString 512 b a) (ByteString 512 b a)
    , Blake2bSig b a
    , Concat (ByteString 8 b a) (ByteString 512 b a)
    , FromConstant Natural (ByteString 0 b a)
    , FromConstant Natural (ByteString 8 b a)
    , Eq (b 512 a)
    ) => Spec
blake2bSimple =
    let a = blake2b_512 $ fromConstant @Natural @(ByteString 0 b a) 0
        b = hash 64 BI.empty BI.empty
    in  it "computes blake2b_512 correctly on empty bytestring" $ a == fromConstant b

blake2bAC :: Spec
blake2bAC =
    let bs = compile @(Zp BLS12_381_Scalar) (blake2b_512 @8 @ArithmeticCircuit @(Zp BLS12_381_Scalar)) :: ByteString 512 ArithmeticCircuit (Zp BLS12_381_Scalar)
        ac = pieces @(Zp BLS12_381_Scalar) bs
    in it "simple test with cardano-crypto " $ acSizeN ac == 564239

specBlake2b :: IO ()
specBlake2b = hspec $ describe "BLAKE2b self-test validation" $ do
        blake2bSimple @(Zp BLS12_381_Scalar) @Vector
        -- TODO: make a proper arithmetic circuit test
        -- blake2bAC
