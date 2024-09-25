{-# LANGUAGE AllowAmbiguousTypes #-}




module Tests.Blake2b where

import           Control.Monad                               (forM_)
import           Data.Bits                                   (shiftR)
import           Data.List.Split.Internals                   (splitOn)
import           Data.Proxy
import           GHC.Generics                                (U1)
import           GHC.TypeLits                                (someNatVal)
import           GHC.TypeNats                                hiding (someNatVal)
import           Prelude
import           Test.Hspec
import           Test.QuickCheck.Gen                         (Gen)
import           Test.QuickCheck.Property
import           Text.Regex.TDFA                             ((=~))

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..), (-!))
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number            (value)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit  (ArithmeticCircuit, exec)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Helpers                (with8n, withGcdn8)
import           ZkFold.Symbolic.Interpreter                 (Interpreter (Interpreter))



dataDir :: FilePath
dataDir = "tests/data/blake2bbittestvectors/Blake2b.rsp"


readRSP :: FilePath -> IO [(Natural, Natural, Natural)]
readRSP path = do
    contents <- readFile path
    let parts = filter (\s -> take 3 s == "Len") $ splitOn "\n\n" contents
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
            _                                            -> error "unreachable Len"

        msgS :: String
        msgS = case s =~ ("Msg = ([a-f0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> error "unreachable Msg"

        hashS :: String
        hashS = case s =~ ("Hash = ([a-f0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> error "unreachable Hash"


testAlgorithm' :: forall c.
    ( Symbolic c
    , Eq (c (Vector 512))
    , Show (c (Vector 512))
    ) => FilePath -> IO ()
testAlgorithm' file = do
    testCases <- readRSP dataDir
    hspec $ describe description $
        forM_ testCases $ \(bytes, input, hash) -> do
            let bitMsg = "calculates hash on a message of len = " <> show bytes <> " bytes"
            it bitMsg $ case someNatVal (toInteger bytes) of
                Just (SomeNat (Proxy :: (Proxy n))) -> do
                    let a = withGcdn8 @n $ blake2b_512 @n @c (with8n @n $ fromConstant @Natural input) :: ByteString 512 c
                    fromConstant hash === a
                Nothing -> error "error with convert an integer into an unknown type-level natural."
    where
        description :: String
        description = "Testing on " <> file

specBlake2bNatural :: IO ()
specBlake2bNatural = testAlgorithm' @(Interpreter (Zp BLS12_381_Scalar)) dataDir


eval :: forall a n . ByteString n (ArithmeticCircuit a U1) -> Vector n a
eval (ByteString bits) = exec bits

toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

specBlake2b' :: forall inputLen. KnownNat inputLen => Spec
specBlake2b' = do
    let n = 8 * value @inputLen
        m = 2 ^ n -! 1
    it ("calculates Blake2b of a " ++ show n ++ "-bit bytestring") $ withMaxSuccess 2 $ do
        x <- toss m
        let hashAC = withGcdn8 @inputLen $ blake2b_512 @inputLen @(ArithmeticCircuit (Zp BLS12_381_Scalar) U1) (with8n @inputLen $ fromConstant @Natural x) :: ByteString 512 (ArithmeticCircuit (Zp BLS12_381_Scalar) U1)
            ByteString (Interpreter hashZP) = withGcdn8 @inputLen $ blake2b_512 @inputLen  @(Interpreter (Zp BLS12_381_Scalar)) (with8n @inputLen $ fromConstant @Natural x)
        pure $ eval @(Zp BLS12_381_Scalar) hashAC === hashZP

specBlake2b :: IO ()
specBlake2b = hspec $ do
    specBlake2b' @0
