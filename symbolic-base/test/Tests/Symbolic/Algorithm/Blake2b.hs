{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Symbolic.Algorithm.Blake2b where

import           Crypto.Hash.BLAKE2.BLAKE2b                  (hash)
import qualified Data.ByteString.Internal                    as BI
import           GHC.Exts                                    (IsString (fromString))
import           GHC.Generics                                hiding (from)
import           Numeric.Natural                             (Natural)
import           Prelude                                     (Eq (..), ($))
import           Test.Hspec                                  (Spec, describe, it)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar, Fr)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b     (blake2b_224, blake2b_512)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compile, eval1)
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.ByteString             (ByteString (..))
import qualified ZkFold.Symbolic.Data.Eq                     as Symbolic
import           ZkFold.Symbolic.Interpreter                 (Interpreter (..))

blake2bNumeric :: forall c . (Symbolic c, Eq (c (Vector 512))) => Spec
blake2bNumeric =
    let a = blake2b_512 @0 @c $ fromConstant (0 :: Natural)
        c = hash 64 BI.empty BI.empty
    in  it "computes blake2b_512 correctly on empty bytestring" $ a == fromConstant c

{-
Appendix A.  Example of BLAKE2b Computation

   We compute the unkeyed hash of three ASCII bytes "abc" with
   BLAKE2b-512 and show internal values during computation.

   BLAKE2b-512("abc") = BA 80 A5 3F 98 1C 4D 0D 6A 27 97 B6 9F 12 F6 E9
                        4C 21 2F 14 68 5A C4 B7 4B 12 BB 6F DB FF A2 D1
                        7D 87 C5 39 2A AB 79 2D C2 52 D5 DE 45 33 CC 95
                        18 D3 8A A8 DB F1 92 5A B9 23 86 ED D4 00 99 23
-}

blake2bExampleRfc :: forall c . (Symbolic c, Eq (c (Vector 512))) => Spec
blake2bExampleRfc =
    let abc' = blake2b_512 @3 @c $ fromConstant $ fromString @BI.ByteString "abc"
        abc  = fromConstant @_ @(ByteString 512 _) $ hash 64 BI.empty "abc"
    in it "example test from rfc7693 " $ abc' == abc

equalityBlake :: forall c . Symbolic c
    => BI.ByteString -> ByteString 24 c -> Bool c
equalityBlake target input = fromConstant target Symbolic.== blake2b_224 @3 @c input

blake2bSymbolic :: Spec
blake2bSymbolic =
    let ac :: ArithmeticCircuit Fr (U1 :*: U1) (Vector 24 :*: U1) Par1
        ac    = compile @Fr $ equalityBlake $ hash 28 BI.empty "abc"
        ByteString bs = fromConstant @_ @(ByteString 24 (Interpreter Fr)) $ fromString @BI.ByteString "abc"
        input         = runInterpreter bs
    in it "simple test with cardano-crypto " $ eval1 ac (U1 :*: U1) (input :*: U1) == 1

specBlake2b :: Spec
specBlake2b = describe "BLAKE2b self-test validation" $ do
    blake2bNumeric @(Interpreter (Zp BLS12_381_Scalar))
    blake2bExampleRfc @(Interpreter (Zp BLS12_381_Scalar))
    blake2bSymbolic
