module ZkFold.Symbolic.Cardano.Builtins where

import           Codec.Serialise              (Serialise (..), serialise)
import qualified Data.ByteString              as BS
import qualified Data.ByteString.Lazy         as BSL
import           Data.Coerce                  (coerce)
import           Data.Text                    (Text)
import qualified Data.Text.Encoding           as Text
import           Prelude                      (Bool (..), Eq (..), Functor (..), Integer, Integral (..), Monoid (..),
                                               Num (..), Ord (..), Semigroup (..), Show (..), fromIntegral, ($), (<$>))
import qualified Prelude                      as Haskell

import qualified ZkFold.Symbolic.Cardano.Data as PLC
import           ZkFold.Symbolic.Cardano.Data (Data)

newtype BuiltinData = BuiltinData Data

instance Haskell.Show BuiltinData where
    show (BuiltinData d) = show d
instance Haskell.Eq BuiltinData where
    (==) (BuiltinData d) (BuiltinData d') = (==) d d'
instance Haskell.Ord BuiltinData where
    compare (BuiltinData d) (BuiltinData d') = compare d d'

newtype BuiltinByteString = BuiltinByteString BS.ByteString

instance Haskell.Show BuiltinByteString where
    show (BuiltinByteString bs) = show bs
instance Haskell.Eq BuiltinByteString where
    (==) (BuiltinByteString bs) (BuiltinByteString bs') = (==) bs bs'
instance Haskell.Ord BuiltinByteString where
    compare (BuiltinByteString bs) (BuiltinByteString bs') = compare bs bs'
instance Haskell.Semigroup BuiltinByteString where
    (<>) (BuiltinByteString bs) (BuiltinByteString bs') = BuiltinByteString $ (<>) bs bs'
instance Haskell.Monoid BuiltinByteString where
    mempty = BuiltinByteString mempty
instance Serialise BuiltinByteString where
    encode (BuiltinByteString bs) = encode bs
    decode = BuiltinByteString <$> decode

serialiseData :: BuiltinData -> BuiltinByteString
serialiseData (BuiltinData b) = BuiltinByteString $ BSL.toStrict $ serialise b
