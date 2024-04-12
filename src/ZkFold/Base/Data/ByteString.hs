module ZkFold.Base.Data.ByteString
  ( Binary (..)
  , toByteString
  , fromByteString
  , putWord8
  , getWord8
  ) where

import           Data.Binary
import           Data.Binary.Get
import           Data.Binary.Put
import qualified Data.ByteString      as Strict
import qualified Data.ByteString.Lazy as Lazy
import           Prelude

toByteString :: Binary a => a -> Strict.ByteString
toByteString = Lazy.toStrict . runPut . put

fromByteString :: Binary a => Strict.ByteString -> Maybe a
fromByteString x = case runGetOrFail get (Lazy.fromStrict x) of
  Left _ -> Nothing
  Right (leftover, _, a) ->
    if Lazy.null leftover then Just a else Nothing
