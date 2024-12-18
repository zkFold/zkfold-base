module Tests.Binary (specBinary) where

import           Data.Binary
import           Prelude
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1, BLS12_381_G2, BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.BN254     (BN254_G1, BN254_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (CompressedPoint, Point)
import           ZkFold.Base.Algebra.EllipticCurve.Pasta     (Pallas, Vesta)
import           ZkFold.Base.Data.ByteString                 (LittleEndian, fromByteString, toByteString)

doesRoundtrip :: (Binary a, Eq a, Show a) => a -> Property
doesRoundtrip x = do
    let xEncoded = toByteString x
    let xDecoded = fromByteString xEncoded
    xDecoded === Just x

specBinary :: IO ()
specBinary = hspec $ describe "Binary instance" $ do
  prop "roundtrips LittleEndian"                 $ doesRoundtrip @LittleEndian
  prop "roundtrips Zp BLS12_381_Scalar"          $ doesRoundtrip @(Zp BLS12_381_Scalar)
  prop "roundtrips Point BN254_G1"               $ doesRoundtrip @(Point BN254_G1)
  prop "roundtrips Point BN254_G2"               $ doesRoundtrip @(Point BN254_G2)
  prop "roundtrips Point BLS12_381_G1"           $ doesRoundtrip @(Point BLS12_381_G1)
  prop "roundtrips CompressedPoint BLS12_381_G1" $ doesRoundtrip @(CompressedPoint BLS12_381_G1)
  prop "roundtrips Point BLS12_381_G2"           $ doesRoundtrip @(Point BLS12_381_G2)
  prop "roundtrips CompressedPoint BLS12_381_G2" $ doesRoundtrip @(CompressedPoint BLS12_381_G2)
  prop "roundtrips Point Pallas"                 $ doesRoundtrip @(Point Pallas)
  prop "roundtrips Point Vesta"                  $ doesRoundtrip @(Point Vesta)
