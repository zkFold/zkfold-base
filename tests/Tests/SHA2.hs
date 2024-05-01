{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.SHA2 (specSHA2Natural, specSHA2) where

import           Control.Monad                               (forM_)
import           Data.Bits                                   (shiftR)
import           Data.Function                               (($))
import           Data.Functor                                ((<$>))
import           Data.List                                   (isPrefixOf, isSuffixOf, take, (++))
import           Data.List.Split                             (splitOn)
import           Data.Proxy                                  (Proxy (..))
import           GHC.TypeLits                                (KnownSymbol, Symbol, symbolVal)
import           Numeric.Natural                             (Natural)
import           Prelude                                     (String, fmap, mod, otherwise, pure, read, (<>), (==))
import qualified Prelude                                     as Haskell
import           System.Directory                            (listDirectory)
import           System.FilePath.Posix
import           System.IO                                   (IO)
import           Test.Hspec                                  (Spec, describe, hspec, shouldBe)
import           Test.QuickCheck                             (Gen, (===))
import           Tests.ArithmeticCircuit                     (eval', it)
import           Text.Regex.TDFA

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              (chooseNatural)
import           ZkFold.Symbolic.Algorithms.Hash.SHA2        (AlgorithmSetup (..), SHA2, SHA2N, sha2, sha2Natural)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString

-- | These test files are provided by the Computer Security Resource Center.
-- Passing these tests is a requirement for having an implementation of a hashing function officially validated.
-- https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Secure-Hashing#shavs
--
dataDir :: FilePath
dataDir = "tests/data/shabittestvectors/"

getTestFiles :: forall (algorithm :: Symbol) . KnownSymbol algorithm => IO [FilePath]
getTestFiles = Haskell.filter isAlgoFile <$> listDirectory dataDir
    where
        isAlgoFile :: String -> Haskell.Bool
        isAlgoFile s = (algorithm `isPrefixOf` s) && not ((algorithm <> "_") `isPrefixOf` s) && (".rsp" `isSuffixOf` s)

        algorithm :: String
        algorithm = fmap (\c -> if c == '/' then '_' else c) $ symbolVal (Proxy @algorithm)

readRSP :: FilePath -> IO [(Natural, Natural, Natural)]
readRSP path = do
    contents <- Haskell.readFile path
    let parts = Haskell.filter (\s -> take 3 s == "Len") $ splitOn "\r\n\r\n" contents
    pure $ readTestCase <$> parts

readTestCase :: String -> (Natural, Natural, Natural)
readTestCase s = (numBits, msg, hash)
    where
        numBits :: Natural
        numBits = read numBitsS

        msgShift :: Haskell.Int
        msgShift
          | numBits `mod` 8 == 0 = 0
          | otherwise = 8 Haskell.- (Haskell.fromIntegral $ numBits `mod` 8)

        msg :: Natural
        msg = read ("0x" ++ msgS) `shiftR` msgShift

        hash :: Natural
        hash = read ("0x" ++ hashS)

        numBitsS :: String
        numBitsS = case s =~ ("Len = ([0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> Haskell.error "unreachable"

        msgS :: String
        msgS = case s =~ ("Msg = ([a-f0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> Haskell.error "unreachable"

        hashS :: String
        hashS = case s =~ ("MD = ([a-f0-9]+)" :: String) of
            (_ :: String, _ :: String, _ :: String, [x]) -> x
            _                                            -> Haskell.error "unreachable"


testAlgorithm
    :: forall (algorithm :: Symbol) element
    .  KnownSymbol algorithm
    => SHA2N algorithm element
    => ToConstant element Natural
    => FilePath
    -> IO ()
testAlgorithm file = do
    testCases <- readRSP $ dataDir </> file
    hspec $ describe description $
        forM_ testCases $ \(bits, input, hash) -> do
            let bitMsg = "calculates hash on a message of " <> Haskell.show bits <> " bits"
            it bitMsg $ toConstant (sha2Natural @algorithm @element bits input) `shouldBe` hash
    where
        description :: String
        description = "Testing " <> symbolVal (Proxy @algorithm) <> " on " <> file

-- | Test the implementation of a hashing algorithm with @Zp BLS12_381_Scalar@ as base field for ByteStrings.
--
specSHA2Natural
    :: forall (algorithm :: Symbol) element
    .  KnownSymbol algorithm
    => SHA2N algorithm element
    => ToConstant element Natural
    => IO ()
specSHA2Natural = do
    testFiles <- getTestFiles @algorithm
    forM_ testFiles $ testAlgorithm @algorithm @element


toss :: Natural -> Gen Natural
toss x = chooseNatural (0, x)

eval :: forall a n . ByteString n (ArithmeticCircuit a) -> ByteString n a
eval (ByteString bits) = ByteString (fmap eval' bits)

specSHA2bs
    :: forall (n :: Natural) (algorithm :: Symbol)
    .  KnownSymbol algorithm
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) n
    => SHA2N algorithm (Zp BLS12_381_Scalar)
    => Spec
specSHA2bs = do
    let n = value @n
        m = 2 ^ n -! 1
    it ("calculates " <> symbolVal (Proxy @algorithm) <> " of a " <> Haskell.show n <> "-bit bytestring") $ do
        x <- toss m
        let hashAC = sha2 @algorithm @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @n $ fromConstant x
            hashZP = sha2Natural @algorithm @(Zp BLS12_381_Scalar) n x
        pure $ eval @(Zp BLS12_381_Scalar) @(ResultSize algorithm) hashAC === hashZP


-- | Test the implementation of a hashing algorithm with @ArithmeticCircuit (Zp BLS12_381_Scalar)@ as base field for ByteStrings.
--
specSHA2
    :: forall (algorithm :: Symbol)
    .  KnownSymbol algorithm
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 1
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 2
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 3
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 4
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 10
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 63
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 64
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 900
    => SHA2 algorithm (ArithmeticCircuit (Zp BLS12_381_Scalar)) 1900
    => SHA2N algorithm (Zp BLS12_381_Scalar)
    => IO ()
specSHA2 = hspec $ do
    specSHA2bs @1    @algorithm
    specSHA2bs @2    @algorithm
    specSHA2bs @3    @algorithm
    specSHA2bs @4    @algorithm
    specSHA2bs @10   @algorithm
    specSHA2bs @63   @algorithm
    specSHA2bs @64   @algorithm
    specSHA2bs @900  @algorithm
    specSHA2bs @1900 @algorithm
