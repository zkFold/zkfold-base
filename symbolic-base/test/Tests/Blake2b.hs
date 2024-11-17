{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Blake2b where

import           Crypto.Hash.BLAKE2.BLAKE2b                  (hash)
import qualified Data.ByteString.Internal                    as BI
import           Data.Data                                   (Proxy (Proxy))
import           GHC.Generics                                (U1, (:*:))
import           Numeric.Natural                             (Natural)
import           Prelude                                     (Eq (..), IO, ($))
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString             (ByteString)
import           ZkFold.Symbolic.Data.Class                  (pieces)
import           ZkFold.Symbolic.Interpreter                 (Interpreter)

-- TODO: We need a proper test for both numeric and symbolic blake2b hashing

blake2bSimple :: forall c .
    ( Symbolic c, Eq (c (Vector 512))) => Spec
blake2bSimple =
    let a = blake2b_512 @0 @c $ fromConstant (0 :: Natural)
        c = hash 64 BI.empty BI.empty
    in  it "computes blake2b_512 correctly on empty bytestring" $ a == fromConstant c

blake2bAC :: Spec
blake2bAC =
    let cs = compile blake2b_512 :: ByteString 512 (ArithmeticCircuit (Zp BLS12_381_Scalar) U1 (Vector 8 :*: U1))
        ac = pieces cs Proxy
    in it "simple test with cardano-crypto " $ acSizeN ac == 564239

specBlake2b :: IO ()
specBlake2b = hspec $ describe "BLAKE2b self-test validation" $ do
        blake2bSimple @(Interpreter (Zp BLS12_381_Scalar))
        -- TODO: make a proper arithmetic circuit test
        -- blake2bAC
