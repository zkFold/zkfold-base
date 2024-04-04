{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Tx where

import           Prelude                        hiding ((*), (+), length, splitAt)
import           Control.Monad.State.Lazy              (evalState, state)

import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Cardano.Types.Address
import           ZkFold.Prelude                        (length, splitAt)

data Transaction inputs rinputs outputs datum x = Transaction
    { txId :: TxId x
    , txFee :: UInt 64 x
    , txForge :: UInt 64 x
    , txReferenceInputs :: Vector rinputs (Input datum x)
    , txInputs :: Vector inputs (Input datum x)
    , txOutputs :: Vector outputs (Output x)
    , txValidityInterval :: (UTCTime x, UTCTime x)
    -- , txDatumWitnesses :: x
    } deriving Eq

instance
    ( Finite inputs
    , Finite rinputs
    , Finite outputs
    , Arithmetizable a x
    , Arithmetizable a (datum x)
    , Arithmetizable a (UInt 11 x)
    , Arithmetizable a (UInt 32 x)
    , Arithmetizable a (UInt 64 x)
    ) => Arithmetizable a (Transaction inputs rinputs outputs datum x) where

    arithmetize (Transaction tid inputs rinputs outputs fee forge vr) =
        (\i fee' forge' is ris os vr' -> i <> fee' <> forge' <> is <> ris <> os <> vr')
            <$> arithmetize tid
            <*> arithmetize fee
            <*> arithmetize forge
            <*> arithmetize inputs
            <*> arithmetize rinputs
            <*> arithmetize outputs
            <*> arithmetize vr

    restore address =
        if length address == typeSize @a @(Transaction inputs rinputs outputs datum x)
        then flip evalState address $ Transaction
            <$> do restore <$> do state . splitAt $ typeSize @a @(TxId x)
            <*> do restore <$> do state . splitAt $ typeSize @a @(UInt 64 x)
            <*> do restore <$> do state . splitAt $ typeSize @a @(UInt 64 x)
            <*> do restore <$> do state . splitAt $ typeSize @a @(Vector inputs (Input datum x))
            <*> do restore <$> do state . splitAt $ typeSize @a @(Vector rinputs (Input datum x))
            <*> do restore <$> do state . splitAt $ typeSize @a @(Vector outputs (Output x))
            <*> do restore <$> do state . splitAt $ typeSize @a @(UTCTime x, UTCTime x)
        else error "restore Transaction: wrong number of arguments"

    typeSize = typeSize @a @(TxId x)
             + typeSize @a @(Vector rinputs (Input datum x))
             + typeSize @a @(Vector inputs (Input datum x))
             + typeSize @a @(Vector outputs (Output x))

newtype TxId x = TxId x
    deriving Eq

instance Arithmetizable a x => Arithmetizable a (TxId x) where

    arithmetize (TxId x) = arithmetize x

    restore tx
        | length tx == typeSize @a @(TxId x) = TxId $ restore tx
        | otherwise = error "restore TxId: wrong number of arguments"

    typeSize = typeSize @a @x

data Input datum a = Input
    { txiOutputRef :: OutputRef a
    -- TODO: should be `Script a`
    , txiValidator :: a
    , txiDatum :: datum a
    -- TODO: should be sometning else
    , txiRedeemer :: a
    } deriving Eq

instance (Arithmetizable a x, Arithmetizable a (UInt 32 x), Arithmetizable a (datum x))
    => Arithmetizable a (Input datum x) where

    arithmetize (Input o v d r) =
        (\o' v' d' r' -> o' <> v' <> d' <> r')
            <$> arithmetize o
            <*> arithmetize v
            <*> arithmetize d
            <*> arithmetize r

    restore i = flip evalState i $ Input
        <$> do restore <$> do state . splitAt $ typeSize @a @(OutputRef x)
        <*> do restore <$> do state . splitAt $ typeSize @a @x
        <*> do restore <$> do state . splitAt $ typeSize @a @(datum x)
        <*> do restore <$> do state . splitAt $ typeSize @a @x

    typeSize = typeSize @a @(OutputRef x)
             + typeSize @a @x
             + typeSize @a @(datum x)
             + typeSize @a @x

data Output a = Output
    { txoAddress :: Address a
    , txoValue :: UInt 64 a
    -- TODO: replace with `Bytes x` or `DatumHash x`
    , txoDatumHash :: a
    } deriving Eq

instance (Arithmetizable a x, Arithmetizable a (UInt 64 x)) => Arithmetizable a (Output x) where

    arithmetize (Output o v d) =
        (\o' v' d' -> o' <> v' <> d')
            <$> arithmetize o
            <*> arithmetize v
            <*> arithmetize d

    restore o = flip evalState o $ Output
        <$> do restore <$> do state . splitAt $ typeSize @a @(Address x)
        <*> do restore <$> do state . splitAt $ typeSize @a @(UInt 64 x)
        <*> do restore <$> do state . splitAt $ typeSize @a @x

    typeSize = typeSize @a @(Address x)
             + typeSize @a @(UInt 64 x)
             + typeSize @a @x

data OutputRef a = OutputRef
    { txoId :: TxId a
    , txoIndex :: UInt 32 a
    } deriving Eq

instance (Arithmetizable a (UInt 32 x), Arithmetizable a x) => Arithmetizable a (OutputRef x) where

    arithmetize (OutputRef txid index) = (<>)
        <$> arithmetize txid
        <*> arithmetize index

    restore outputRef = flip evalState outputRef $ OutputRef
        <$> do restore <$> do state . splitAt $ typeSize @a @(TxId x)
        <*> do restore <$> do state . splitAt $ typeSize @a @(UInt 32 x)

    typeSize = typeSize @a @(TxId x)
             + typeSize @a @(UInt 32 x)
