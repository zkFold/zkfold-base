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
-- import qualified ZkFold.Symbolic.Algorithms.Hash.Blake2b as Hash

newtype BuiltinBool = BuiltinBool Bool

true :: BuiltinBool
true = BuiltinBool True

false :: BuiltinBool
false = BuiltinBool False

ifThenElse :: BuiltinBool -> a -> a -> a
ifThenElse (BuiltinBool b) x y = if b then x else y

newtype BuiltinUnit = BuiltinUnit ()

unitval :: BuiltinUnit
unitval = BuiltinUnit ()

chooseUnit :: BuiltinUnit -> a -> a
chooseUnit (BuiltinUnit ()) a = a

type BuiltinInteger = Integer

addInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
addInteger = coerce ((+) @Integer)

subtractInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
subtractInteger = coerce ((-) @Integer)

multiplyInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
multiplyInteger = coerce ((*) @Integer)

divideInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
divideInteger = coerce (div @Integer)

modInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
modInteger = coerce (mod @Integer)

quotientInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
quotientInteger = coerce (quot @Integer)

remainderInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinInteger
remainderInteger = coerce (rem @Integer)

lessThanInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanInteger x y = BuiltinBool $ coerce ((<) @Integer) x  y

lessThanEqualsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
lessThanEqualsInteger x y = BuiltinBool $ coerce ((<=) @Integer) x y

equalsInteger :: BuiltinInteger -> BuiltinInteger -> BuiltinBool
equalsInteger x y = BuiltinBool $ coerce ((==) @Integer) x y

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

appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinByteString $ BS.append b1 b2

consByteString :: BuiltinInteger -> BuiltinByteString -> BuiltinByteString
consByteString n (BuiltinByteString b) = BuiltinByteString $ BS.cons (fromIntegral n) b

sliceByteString :: BuiltinInteger -> BuiltinInteger -> BuiltinByteString -> BuiltinByteString
sliceByteString start n (BuiltinByteString b) = BuiltinByteString $ BS.take (fromIntegral n) (BS.drop (fromIntegral start) b)

lengthOfByteString :: BuiltinByteString -> BuiltinInteger
lengthOfByteString (BuiltinByteString b) = toInteger $ BS.length b

indexByteString :: BuiltinByteString -> BuiltinInteger -> BuiltinInteger
indexByteString (BuiltinByteString b) i = toInteger $ BS.index b (fromInteger i)

emptyByteString :: BuiltinByteString
emptyByteString = BuiltinByteString BS.empty

{-
blake2b_224 :: BuiltinByteString -> BuiltinByteString
blake2b_224 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_224 b

blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 (BuiltinByteString b) = BuiltinByteString $ Hash.blake2b_256 b
-}

equalsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
equalsByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 == b2

lessThanByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 < b2

lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinBool
lessThanEqualsByteString (BuiltinByteString b1) (BuiltinByteString b2) = BuiltinBool $ b1 <= b2

decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 (BuiltinByteString b) = BuiltinString $ Text.decodeUtf8 b

newtype BuiltinString = BuiltinString Text

newtype BuiltinPair a b = BuiltinPair (a, b)

newtype BuiltinList a = BuiltinList [a]

instance Haskell.Show a => Haskell.Show (BuiltinList a) where
    show (BuiltinList l) = show l
instance Haskell.Eq a => Haskell.Eq (BuiltinList a) where
    (==) (BuiltinList l) (BuiltinList l') = (==) l l'
instance Haskell.Ord a => Haskell.Ord (BuiltinList a) where
    compare (BuiltinList l) (BuiltinList l') = compare l l'

null :: BuiltinList a -> BuiltinBool
null (BuiltinList (_:_)) = BuiltinBool False
null (BuiltinList [])    = BuiltinBool True

head :: BuiltinList a -> a
head (BuiltinList (x:_)) = x
head (BuiltinList [])    = Haskell.error "empty list"

tail :: BuiltinList a -> BuiltinList a
tail (BuiltinList (_:xs)) = BuiltinList xs
tail (BuiltinList [])     = Haskell.error "empty list"

chooseList :: BuiltinList a -> b -> b -> b
chooseList (BuiltinList [])    b1 _ = b1
chooseList (BuiltinList (_:_)) _ b2 = b2

mkNilData :: BuiltinUnit -> BuiltinList BuiltinData
mkNilData _ = BuiltinList []

mkNilPairData :: BuiltinUnit -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
mkNilPairData _ = BuiltinList []

mkCons :: a -> BuiltinList a -> BuiltinList a
mkCons a (BuiltinList as) = BuiltinList (a:as)

newtype BuiltinData = BuiltinData Data

instance Haskell.Show BuiltinData where
    show (BuiltinData d) = show d
instance Haskell.Eq BuiltinData where
    (==) (BuiltinData d) (BuiltinData d') = (==) d d'
instance Haskell.Ord BuiltinData where
    compare (BuiltinData d) (BuiltinData d') = compare d d'

-- | Convert a 'BuiltinData' into a 'PLC.Data'. Only works off-chain.
builtinDataToData :: BuiltinData -> PLC.Data
builtinDataToData (BuiltinData d) = d

-- | Convert a 'PLC.Data' into a 'BuiltinData'. Only works off-chain.
dataToBuiltinData :: PLC.Data -> BuiltinData
dataToBuiltinData = BuiltinData

chooseData :: forall a . BuiltinData -> a -> a -> a -> a -> a -> a
chooseData (BuiltinData d) constrCase mapCase listCase iCase bCase = case d of
    PLC.Constr{} -> constrCase
    PLC.Map{}    -> mapCase
    PLC.List{}   -> listCase
    PLC.I{}      -> iCase
    PLC.B{}      -> bCase

mkConstr :: BuiltinInteger -> BuiltinList BuiltinData -> BuiltinData
mkConstr i (BuiltinList args) = BuiltinData (PLC.Constr i (fmap builtinDataToData args))

mkMap :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> BuiltinData
mkMap (BuiltinList es) = BuiltinData (PLC.Map (fmap p2p es))
  where
      p2p (BuiltinPair (d, d')) = (builtinDataToData d, builtinDataToData d')

mkList :: BuiltinList BuiltinData -> BuiltinData
mkList (BuiltinList l) = BuiltinData (PLC.List (fmap builtinDataToData l))

mkI :: BuiltinInteger -> BuiltinData
mkI i = BuiltinData (PLC.I i)

mkB :: BuiltinByteString -> BuiltinData
mkB (BuiltinByteString b) = BuiltinData (PLC.B b)

unsafeDataAsConstr :: BuiltinData -> BuiltinPair BuiltinInteger (BuiltinList BuiltinData)
unsafeDataAsConstr (BuiltinData (PLC.Constr i args)) = BuiltinPair (i, BuiltinList $ fmap dataToBuiltinData args)
unsafeDataAsConstr _                                 = Haskell.error "not a Constr"

unsafeDataAsMap :: BuiltinData -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
unsafeDataAsMap (BuiltinData (PLC.Map m)) = BuiltinList (fmap p2p m)
  where
      p2p (d, d') = BuiltinPair (dataToBuiltinData d, dataToBuiltinData d')
unsafeDataAsMap _                         = Haskell.error "not a Map"

unsafeDataAsList :: BuiltinData -> BuiltinList BuiltinData
unsafeDataAsList (BuiltinData (PLC.List l)) = BuiltinList (fmap dataToBuiltinData l)
unsafeDataAsList _                          = Haskell.error "not a List"

unsafeDataAsI :: BuiltinData -> BuiltinInteger
unsafeDataAsI (BuiltinData (PLC.I i)) = i
unsafeDataAsI _                       = Haskell.error "not an I"

unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB (BuiltinData (PLC.B b)) = BuiltinByteString b
unsafeDataAsB _                       = Haskell.error "not a B"

equalsData :: BuiltinData -> BuiltinData -> BuiltinBool
equalsData (BuiltinData b1) (BuiltinData b2) = BuiltinBool $ b1 Haskell.== b2

serialiseData :: BuiltinData -> BuiltinByteString
serialiseData (BuiltinData b) = BuiltinByteString $ BSL.toStrict $ serialise b
