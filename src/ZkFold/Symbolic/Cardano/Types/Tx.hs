{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.Tx where

import           Prelude                        hiding ((*), (+), length, splitAt)
import           Control.Monad.State.Lazy              (evalState, state)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Cardano.Types.Address
import           ZkFold.Prelude                        (length, splitAt)

data Transaction inputs outputs datum x = Transaction
    { txId :: TxId x
    , txInputs :: Vector inputs (Address x)
    , txOutputs :: Vector outputs (Address x)
    , txDatum :: datum x
    } deriving Eq

instance (Finite inputs, Finite outputs, Arithmetizable a x, Arithmetizable a (datum x))
    => Arithmetizable a (Transaction inputs outputs datum x) where

    arithmetize (Transaction tid inputs outputs datum) =
        (\i is os d -> i <> is <> os <> d)
            <$> arithmetize tid
            <*> arithmetize inputs
            <*> arithmetize outputs
            <*> arithmetize datum

    restore address =
        if length address == typeSize @a @(Transaction inputs outputs datum x)
        then flip evalState address $ Transaction
            <$> do restore <$> do state . splitAt $ typeSize @a @(TxId x)
            <*> do restore <$> do state . splitAt $ typeSize @a @(Vector inputs (Address x))
            <*> do restore <$> do state . splitAt $ typeSize @a @(Vector outputs (Address x))
            <*> do restore <$> do state . splitAt $ typeSize @a @(datum x)
        else error "restore Transaction: wrong number of arguments"

    typeSize = typeSize @a @(TxId x)
             + typeSize @a @(Vector inputs (Address x))
             + typeSize @a @(Vector outputs (Address x))
             + typeSize @a @(datum x)

newtype TxId x = TxId x
    deriving Eq

instance Arithmetizable a x => Arithmetizable a (TxId x) where

    arithmetize (TxId x) = arithmetize x

    restore tx
        | length tx == typeSize @a @(TxId x) = TxId $ restore tx
        | otherwise = error "restore TxId: wrong number of arguments"

    typeSize = typeSize @a @x
