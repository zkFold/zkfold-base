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

newtype BuiltinBool = BuiltinBool Bool

newtype BuiltinUnit = BuiltinUnit ()

unitval :: BuiltinUnit
unitval = BuiltinUnit ()

type BuiltinInteger = Integer

newtype BuiltinByteString = BuiltinByteString BS.ByteString

newtype BuiltinString = BuiltinString Text

newtype BuiltinPair a b = BuiltinPair (a, b)

newtype BuiltinList a = BuiltinList [a]

mkNilData :: BuiltinUnit -> BuiltinList BuiltinData
mkNilData _ = BuiltinList []

mkCons :: a -> BuiltinList a -> BuiltinList a
mkCons a (BuiltinList as) = BuiltinList (a:as)

newtype BuiltinData = BuiltinData Data

-- | Convert a 'BuiltinData' into a 'PLC.Data'. Only works off-chain.
builtinDataToData :: BuiltinData -> PLC.Data
builtinDataToData (BuiltinData d) = d

mkConstr :: BuiltinInteger -> BuiltinList BuiltinData -> BuiltinData
mkConstr i (BuiltinList args) = BuiltinData (PLC.Constr i (fmap builtinDataToData args))

mkList :: BuiltinList BuiltinData -> BuiltinData
mkList (BuiltinList l) = BuiltinData (PLC.List (fmap builtinDataToData l))

mkI :: BuiltinInteger -> BuiltinData
mkI i = BuiltinData (PLC.I i)

mkB :: BuiltinByteString -> BuiltinData
mkB (BuiltinByteString b) = BuiltinData (PLC.B b)

equalsData :: BuiltinData -> BuiltinData -> BuiltinBool
equalsData (BuiltinData b1) (BuiltinData b2) = BuiltinBool $ b1 Haskell.== b2
