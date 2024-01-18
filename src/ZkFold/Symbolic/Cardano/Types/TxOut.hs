{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.TxOut where

import           Prelude                          (Eq (..), ($), error, otherwise)

import           ZkFold.Symbolic.Arithmetization (Arithmetizable(..))
import           ZkFold.Prelude                  (length)

newtype DatumHash x = DatumHash x

instance Arithmetizable a x => Arithmetizable a (DatumHash x) where
    arithmetize (DatumHash x) = arithmetize x

    restore datum
        | length datum == typeSize @a @(DatumHash x) = DatumHash $ restore datum
        | otherwise = error "restore DatumHash: wrong number of arguments"

    typeSize = typeSize @a @x