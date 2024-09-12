{-# LANGUAGE AllowAmbiguousTypes #-}

module Tests.Blake2b where

import           Numeric.Natural                             (Natural)
import           Test.Hspec
import qualified Crypto.Hash.BLAKE2.BLAKE2b as B2b

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Interpreter                 (Interpreter)
import Prelude (Eq (..), IO, ($), (.))
import           Test.QuickCheck                             ((===))
import GHC.Show (Show)
import qualified Data.ByteString as BI

-- TODO: We need a proper test for both numeric and symbolic blake2b hashing
specBlake2b_512 :: forall c .
    ( Symbolic c, Eq (c (Vector 512)), Show (c (Vector 512))) => IO ()
specBlake2b_512 = hspec $ do
    describe "Blake2b - 512 bits specification" $ do
        it "hashed string is \"\" " $ do
            let s = ""
                a = blake2b_512 @0 @c $ fromConstant @Natural (toNatural . hexDecode $ s)
                answer = B2b.hash 64 "" $ hexDecode s   -- key is second param, change \"\" to key64'
                -- right answer for key64 = hexDecode "10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568"
            a === fromConstant answer 

        it "hashed string is 2 \"00\" " $ do
            let s = "00"
                a = blake2b_512 @1 @c $ fromConstant @Natural (toNatural . hexDecode $ s)
                answer = B2b.hash 64 "" $ hexDecode s
                -- right answer for empty key = hexDecode "2fa3f686df876995167e7c2e5d74c4c7b6e48f8068fe0e44208344d480f7904c36963e44115fe3eb2a3ac8694c28bcb4f5a0f3276f2e79487d8219057a506e4b"
            a === fromConstant answer 

key64' :: BI.ByteString 
key64' = hexDecode "000102030405060708090a0b0c0d0e0f\
                  \101112131415161718191a1b1c1d1e1f\
                  \202122232425262728292a2b2c2d2e2f\
                  \303132333435363738393a3b3c3d3e3f"



specBlake2b' :: forall c .
    ( Symbolic c, Eq (c (Vector 512)), Show (c (Vector 512))) => IO ()
specBlake2b' = do
    -- specBlake2b_228
    -- specBlake2b_256
    specBlake2b_512 @c


specBlake2b :: IO ()
specBlake2b = do
        specBlake2b' @(Interpreter (Zp BLS12_381_Scalar))
        -- blake2bSimple @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 8))
