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
import           ZkFold.Symbolic.Data.ByteString             (ByteString, Concat, ToWords (..), Truncate (..))
import           ZkFold.Symbolic.Data.Combinators            (Extend)

blake2bSimple :: forall a b .
    ( Blake2bSig b a
    , ToWords (ByteString 64 b a) (ByteString 64 b a)
    , Concat (ByteString 8 b a) (ByteString 256 b a)
    , Truncate (ByteString 512 b a) (ByteString 256 b a)
    , Extend (ByteString 0 b a) (ByteString 64 b a)
    , FromConstant Natural (ByteString 0 b a)
    , FromConstant Natural (ByteString 8 b a)
    , Eq (b 256 a)) => Spec
blake2bSimple =
    let a = blake2b_256 $ fromConstant @Natural @(ByteString 0 b a) 0
        b = hash 32 BI.empty BI.empty
    in  it "simple test with cardano-crypto " $ a == fromConstant b

specBlake2b :: IO ()
specBlake2b = hspec $ describe "BLAKE2b self-test validation" $ do
        blake2bSimple @(Zp BLS12_381_Scalar) @Vector
