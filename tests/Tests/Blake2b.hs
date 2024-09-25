-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}




module Tests.Blake2b where

import           Test.Hspec
import qualified Crypto.Hash.BLAKE2.BLAKE2b as B2b

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Interpreter                 (Interpreter)
import           ZkFold.Symbolic.Data.ByteString

import           Prelude
import           Test.QuickCheck                             ((===))
import qualified Data.ByteString as BI
import           Data.List.Split.Internals                   (splitOn)
import           Data.Bits                                   (shiftR)
import           Control.Monad                               (forM_)
import           GHC.TypeLits                                (someNatVal)
import           Data.Proxy
import           GHC.TypeNats                                hiding (someNatVal)
import Text.Regex.TDFA ((=~))
import ZkFold.Symbolic.Data.Helpers (with8n, withGcdn8)



dataDir :: FilePath
dataDir = "tests/data/blake2bbittestvectors/Blake2b.rsp"


readRSP :: FilePath -> IO [(Natural, Natural, Natural)]
readRSP path = do
    contents <- readFile path
    let parts = filter (\s -> take 3 s == "Len") $ splitOn "\r\n\r\n" contents
    pure $ readTestCase <$> parts

readTestCase :: String -> (Natural, Natural, Natural)
readTestCase s = (numBits, msg, hash)
    where
        numBits :: Natural
        numBits = read numBitsS

        msgShift :: Int
        msgShift
          | numBits `mod` 8 == 0 = 0
          | otherwise = 8 - fromIntegral (numBits `mod` 8)

        msg :: Natural
        msg = read ("0x" ++ msgS) `shiftR` msgShift

        hash :: Natural
        hash = read ("0x" ++ hashS)

        numBitsS :: String
        numBitsS = case s =~ ("Len = ([0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> error "unreachable"

        msgS :: String
        msgS = case s =~ ("Msg = ([a-f0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> error "unreachable"

        hashS :: String
        hashS = case s =~ ("Hash = ([a-f0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> error "unreachable"s


testAlgorithm' :: forall c.
    ( Symbolic c
    , Eq (c (Vector 512))
    , Show (c (Vector 512))
    ) => FilePath -> IO ()
testAlgorithm' file = do
    testCases <- readRSP dataDir
    hspec $ describe description $
        forM_ testCases $ \(bytes, input, hash) -> do
            let bitMsg = "calculates hash on a message of len =  " <> show bytes <> " bytes"
            it bitMsg $ case someNatVal (toInteger bytes) of
                Just (SomeNat (Proxy :: (Proxy n))) -> do
                    let 
                        a = withGcdn8 @n $ blake2b_512 @n @c (with8n @n $ fromConstant @Natural input) :: ByteString 512 c
                        answer = fromConstant @Natural hash :: ByteString 512 c
                    a === fromConstant answer
                Nothing -> error "error with convert an integer into an unknown type-level natural."
                -- right answer for key64 = hexDecode "10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568"
            -- bitMsg $ toConstant (specBlake2b_512 @c bits input) `shouldBe` hash
    where
        description :: String
        description = "Testing on " <> file


-- TODO: We need a proper test for both numeric and symbolic blake2b hashing
specBlake2b_512 :: forall c .
    ( Symbolic c, Eq (c (Vector 512)), Show (c (Vector 512))) => IO ()
specBlake2b_512 = hspec $ do
    -- testAlgorithm @c
    describe "Blake2b - 512 bits specification" $ do
        it "hashed string is \"\" " $ do
            let s = ""
                a = withGcdn8 @0 $ blake2b_512 @0 @c $ fromConstant @Natural (read $ "0x" ++ s)
                -- answer = B2b.hash 64 key64' $ hexDecode ""   -- key is second param, change \"\" to key64'
                answer  = fromConstant @Natural $ read "0x10ebb67700b1868efb4417987acf4690ae9d972fb7a590c2f02871799aaa4786b5e996e8f0f4eb981fc214b005f42d2ff4233499391653df7aefcbc13fc51568"
            a === answer

        -- it "hashed string is 2 \"00\" " $ do
        --     let s = "00"
        --         a = blake2b_512 @1 @c $ fromConstant @Natural (read $ "0x" ++ s)
        --         -- answer = B2b.hash 64 key64' $ hexDecode s
        --         answer  = fromConstant @Natural $ read "0x2fa3f686df876995167e7c2e5d74c4c7b6e48f8068fe0e44208344d480f7904c36963e44115fe3eb2a3ac8694c28bcb4f5a0f3276f2e79487d8219057a506e4b"
        --     a === answer

key64' :: BI.ByteString
key64' = hexDecode "000102030405060708090a0b0c0d0e0f\
                   \101112131415161718191a1b1c1d1e1f\
                   \202122232425262728292a2b2c2d2e2f\
                   \303132333435363738393a3b3c3d3e3f"



specBlake2b' :: forall c .
    ( Symbolic c, Eq (c (Vector 512)), Show (c (Vector 512))) => IO ()
specBlake2b' = do
    specBlake2b_512 @c


specBlake2b :: IO ()
specBlake2b = specBlake2b' @(Interpreter (Zp BLS12_381_Scalar))
        -- blake2bSimple @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 8))
