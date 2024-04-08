{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types where

import           Prelude                        hiding ((*), (+), length, splitAt)
import           Control.Monad.State.Lazy              (evalState, state)

import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Prelude                        (length, splitAt)

data Transaction inputs rinputs outputs tokens datum x = Transaction
    { txReferenceInputs :: Vector rinputs (Input datum x)
    , txInputs :: Vector inputs (Input datum x)
    , txOutputs :: Vector outputs (Output tokens x)
    , txValidityInterval :: (UTCTime x, UTCTime x)
    } deriving Eq

instance
    ( Finite inputs
    , Finite rinputs
    , Finite outputs
    , Finite tokens
    , Arithmetizable a x
    , Arithmetizable a (datum x)
    , Arithmetizable a (UInt 11 x)
    , Arithmetizable a (UInt 32 x)
    , Arithmetizable a (UInt 64 x)
    ) => Arithmetizable a (Transaction inputs rinputs outputs tokens datum x) where

    arithmetize (Transaction inputs rinputs outputs vr) =
        (\is ris os vr' -> is <> ris <> os <> vr')
            <$> arithmetize inputs
            <*> arithmetize rinputs
            <*> arithmetize outputs
            <*> arithmetize vr

    restore address = flip evalState address $ Transaction
        <$> do restore <$> do state . splitAt $ typeSize @a @(Vector inputs (Input datum x))
        <*> do restore <$> do state . splitAt $ typeSize @a @(Vector rinputs (Input datum x))
        <*> do restore <$> do state . splitAt $ typeSize @a @(Vector outputs (Output tokens x))
        <*> do restore <$> do state . splitAt $ typeSize @a @(UTCTime x, UTCTime x)

    typeSize = typeSize @a @(Vector inputs (Input datum x))
             + typeSize @a @(Vector rinputs (Input datum x))
             + typeSize @a @(Vector outputs (Output tokens x))
             + typeSize @a @(UTCTime x, UTCTime x)

newtype TxId x = TxId x
    deriving Eq

instance Arithmetizable a x => Arithmetizable a (TxId x) where

    arithmetize (TxId x) = arithmetize x

    restore tx
        | length tx == typeSize @a @(TxId x) = TxId $ restore tx
        | otherwise = error "restore TxId: wrong number of arguments"

    typeSize = typeSize @a @x

newtype Value n a = Value (Vector n ({- Bytes a-} a, ({- Bytes a -} a, UInt 64 a)))
    deriving Eq

deriving instance
    (Finite n, Arithmetizable i a, Arithmetizable i (UInt 64 a))
    => Arithmetizable i (Value n a)

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

data Output tokens a = Output
    { txoAddress :: Address a
    -- , txoValue :: UInt 64 a
    , txiValue :: Value tokens a
    -- TODO: replace with `Bytes x` or `DatumHash x`
    , txoDatumHash :: a
    } deriving Eq

instance (Finite tokens, Arithmetizable a x, Arithmetizable a (UInt 64 x)) => Arithmetizable a (Output tokens x) where

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

data Address x = Address
    { addrType :: x
    , addrPayCred :: x
    , addrStakeCred :: x
    } deriving Eq

instance Arithmetizable a x => Arithmetizable a (Address x) where
    arithmetize (Address addrType payCred stakeCred) =
        (\t p s -> t <> p <> s)
            <$> arithmetize addrType
            <*> arithmetize payCred
            <*> arithmetize stakeCred
    restore address = flip evalState address $ Address
        <$> do restore <$> do state . splitAt $ typeSize @a @x
        <*> do restore <$> do state . splitAt $ typeSize @a @x
        <*> do restore <$> do state . splitAt $ typeSize @a @x
    typeSize = 3 * typeSize @a @x

-- newtype Address x = Address (x, (x, x))
    -- deriving Eq
    -- deriving (Arithmetizable a) via (x, (x, x))

newtype DatumHash datum a = DatumHash a
    deriving (Eq, Arithmetizable i)

newtype ScriptHash a = ScriptHash a
    deriving (Eq, Arithmetizable i)
