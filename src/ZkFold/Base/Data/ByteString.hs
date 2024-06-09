{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Data.ByteString
  ( Binary (..)
  , toByteString
  , fromByteString
  , putWord8
  , getWord8
  , LittleEndian (..)
  ) where

import           Control.Applicative  (many)
import           Data.Binary
import           Data.Binary.Get
import           Data.Binary.Put
import qualified Data.ByteString      as Strict
import qualified Data.ByteString.Lazy as Lazy
import           Data.Foldable        (foldl')
import           Numeric.Natural      (Natural)
import           Prelude
import           Test.QuickCheck      (Arbitrary (..))

toByteString :: Binary a => a -> Strict.ByteString
toByteString = Lazy.toStrict . runPut . put

fromByteString :: Binary a => Strict.ByteString -> Maybe a
fromByteString x = case runGetOrFail get (Lazy.fromStrict x) of
  Left _ -> Nothing
  Right (leftover, _, a) ->
    if Lazy.null leftover then Just a else Nothing

-- Little-endian encoding for unsigned & unsized integers
-- un little, deux little, trois little endians
newtype LittleEndian = LittleEndian {unLittleEndian :: Natural}
  deriving stock (Read, Show)
  deriving newtype (Eq, Ord, Num, Enum, Real, Integral)
instance Binary LittleEndian where
  get = do
    ns <- many getWord8
    let accum (!pw :: Natural, !acc :: Natural) w8 = (pw * 256, pw * fromIntegral w8 + acc)
        littleEndian = LittleEndian (snd $ foldl' accum (1, 0) ns)
    return littleEndian
  put (LittleEndian n)
    | n == 0 = mempty
    | otherwise =
      let (n', r) = n `divMod` 256
      in putWord8 (fromIntegral r) <> put (LittleEndian n')
instance Arbitrary LittleEndian where
  arbitrary = fromInteger . abs <$> arbitrary
