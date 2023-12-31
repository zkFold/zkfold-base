module ZkFold.Base.Data.ByteString where

import           Data.ByteString (ByteString, cons, uncons, empty)
import           Data.Word       (Word8)
import           Prelude

class ToByteString a where
    toByteString :: a -> ByteString

instance ToByteString ByteString where
    toByteString = id

-- Little-endian encoding for unsigned integers
instance ToByteString Integer where
    toByteString n
        | n < 0     = error "ToByteString: Negative numbers are not supported"
        | n == 0    = empty
        | otherwise =
            let bs = toByteString (n `div` 256)
                b  = fromIntegral (n `mod` 256) :: Word8
            in b `cons` bs

instance (ToByteString a, ToByteString b) => ToByteString (a, b) where
    toByteString (a, b) = toByteString a <> toByteString b

instance ToByteString a => ToByteString [a] where
    toByteString = foldMap toByteString

class FromByteString a where
    fromByteString :: ByteString -> Maybe a

instance FromByteString ByteString where
    fromByteString = Just

instance FromByteString Integer where
    fromByteString bs
        | bs == empty = Just 0
        | otherwise   = do
            (b, bs') <- uncons bs
            let r = fromIntegral b :: Integer
            (r +) . (256 *) <$> fromByteString bs'