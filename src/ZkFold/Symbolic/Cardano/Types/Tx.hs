{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.Tx where

import           Prelude                          (Eq (..), ($), error, otherwise)

import           ZkFold.Symbolic.Compiler
import           ZkFold.Prelude                  (length)

-- TODO (Issue #10): make a proper implementation
newtype Tx x = Tx x

instance Arithmetizable a x => Arithmetizable a (Tx x) where
    arithmetize (Tx x) = arithmetize x

    restore tx
        | length tx == typeSize @a @(Tx x) = Tx $ restore tx
        | otherwise = error "restore Tx: wrong number of arguments"

    typeSize = typeSize @a @x

newtype TxId x = TxId x

instance Arithmetizable a x => Arithmetizable a (TxId x) where
    arithmetize (TxId x) = arithmetize x

    restore txId
        | length txId == typeSize @a @(TxId x) = TxId $ restore txId
        | otherwise = error "restore TxId: wrong number of arguments"

    typeSize = typeSize @a @x