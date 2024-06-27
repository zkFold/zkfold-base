module ZkFold.Symbolic.Cardano.IsData.Class where

import           Data.Kind                        (Type)
import           Prelude                          (Integer, id)

import qualified ZkFold.Symbolic.Cardano.Builtins as BI
import           ZkFold.Symbolic.Cardano.Builtins (builtinDataToData)
import qualified ZkFold.Symbolic.Cardano.Data     as PLC

class ToData (a :: Type) where
    -- | Convert a value to 'BuiltinData'.
    toBuiltinData :: a -> BI.BuiltinData

instance ToData BI.BuiltinData where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = id

instance ToData Integer where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = BI.mkI

instance ToData BI.BuiltinByteString where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = BI.mkB

instance ToData a => ToData [a] where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData l = BI.mkList (mapToBuiltin l)
        where
          {-# INLINE mapToBuiltin #-}
          mapToBuiltin :: [a] -> BI.BuiltinList BI.BuiltinData
          mapToBuiltin = go
            where
                go :: [a] -> BI.BuiltinList BI.BuiltinData
                go []     = BI.mkNilData BI.unitval
                go (x:xs) = BI.mkCons (toBuiltinData x) (go xs)

-- | Convert a value to 'PLC.Data'.
toData :: (ToData a) => a -> PLC.Data
toData a = builtinDataToData (toBuiltinData a)
