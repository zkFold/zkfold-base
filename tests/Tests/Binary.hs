module Tests.Binary (specBinary) where

import           Data.Binary
import           Prelude
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.ByteString                 (LittleEndian, fromByteString, toByteString)

specBinary :: IO ()
specBinary = hspec $ describe "Binary instance" $ do
  prop "roundtrips LittleEndian" $ doesRoundtrip @LittleEndian
  prop "roundtrips Zp BLS12_381_Scalar" $ doesRoundtrip @(Zp BLS12_381_Scalar)

doesRoundtrip :: (Binary a, Eq a, Show a) => a -> Property
doesRoundtrip x = do
    let xEncoded = toByteString x
    let xDecoded = fromByteString xEncoded
    xDecoded === Just x
