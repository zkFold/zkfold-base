{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types where

import           Prelude                          (($), concat, return, error, (++), fst, snd, Eq (..), otherwise)
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Arithmetization (Arithmetizable(..))
import           ZkFold.Symbolic.Data.List       (U32, List)
import           ZkFold.Prelude                  (drop, take, length)

data Datum x = Datum x x x

instance Arithmetizable a x => Arithmetizable a (Datum x) where
    arithmetize (Datum addr vTime ada) = do
        addrAC  <- arithmetize addr
        vTimeAC <- arithmetize vTime
        adaAC   <- arithmetize ada
        return $ concat [addrAC, vTimeAC, adaAC]

    restore datum
        | length datum == typeSize @a @(Datum x) =
            let addrAC  = restore $ take (typeSize @a @x) datum
                vTimeAC = restore $ take (typeSize @a @x) $ drop (typeSize @a @x) datum
                adaAC   = restore $ take (typeSize @a @x) $ drop (typeSize @a @x + typeSize @a @x) datum
            in Datum addrAC vTimeAC adaAC
        | otherwise = error "restore Datum: wrong number of arguments"

    typeSize = 3 * typeSize @a @x

data Redeemer x = Redeemer

instance Arithmetizable a x => Arithmetizable a (Redeemer x) where
    arithmetize Redeemer = return [one]

    restore [] = Redeemer
    restore _  = error "restore Redeemer: wrong number of arguments"

    typeSize = 0

data TxInfo x = TxInfo
    {
        txInfoInputs          :: List U32 x,
        txInfoReferenceInputs :: List U32 x,
        txInfoOutputs         :: List U32 (TxOut x),
        txInfoFee             :: x,
        txInfoMint            :: x,
        txInfoDCert           :: List U32 x,
        txInfoWdrl            :: x,
        txInfoValidRange      :: (x, x),
        txInfoSignatories     :: List U32 x,
        txInfoId              :: x
    }
    -- deriving (Haskell.Show, Haskell.Eq)

instance Arithmetizable a x => Arithmetizable a (TxInfo x) where
    arithmetize (TxInfo inputs referenceInputs outputs fee mint dCert wdrl validRange signatories id) = do
        inputs'          <- arithmetize inputs
        referenceInputs' <- arithmetize referenceInputs
        outputs'         <- arithmetize outputs
        fee'             <- arithmetize fee
        forge'           <- arithmetize mint
        dCert'           <- arithmetize dCert
        wdrl'            <- arithmetize wdrl
        validRange'      <- arithmetize validRange
        signatories'     <- arithmetize signatories
        id'              <- arithmetize id
        return $ concat [inputs', referenceInputs', outputs', fee', forge', dCert', wdrl', validRange', signatories', id']

    restore info
        | length info == typeSize @a @(TxInfo x) =
            let inputs          = restore $ take (typeSize @a @(List U32 x)) info
                referenceInputs = restore $ take (typeSize @a @(List U32 x)) $ drop (typeSize @a @(List U32 x)) info
                outputs         = restore $ take (typeSize @a @(List U32 (TxOut x))) $ drop (2 * typeSize @a @(List U32 x)) info
                fee             = restore $ take (typeSize @a @(List U32 x)) $ drop (2 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x))) info
                mint            = restore $ take (typeSize @a @x) $ drop (2 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + typeSize @a @x) info
                dCert           = restore $ take (typeSize @a @(List U32 x)) $ drop (2 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + 2 * typeSize @a @x) info
                wdrl            = restore $ take (typeSize @a @x) $ drop (3 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + 2 * typeSize @a @x) info
                validRange      = restore $ take (typeSize @a @(x, x)) $ drop (3 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + 3 * typeSize @a @x) info
                signatories     = restore $ take (typeSize @a @(List U32 x)) $ drop (3 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + 3 * typeSize @a @x + typeSize @a @(x, x)) info
                id              = restore $ take (typeSize @a @x) $ drop (4 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + 3 * typeSize @a @x + typeSize @a @(x, x)) info
            in TxInfo inputs referenceInputs outputs fee mint dCert wdrl validRange signatories id
        | otherwise = error "restore TxInfo: wrong number of arguments"

    typeSize = 4 * typeSize @a @(List U32 x) + typeSize @a @(List U32 (TxOut x)) + 4 * typeSize @a @x + typeSize @a @(x, x)

lowerBound :: (x, x) -> x
lowerBound = fst

upperBound :: (x, x) -> x
upperBound = snd

data ScriptContext x = ScriptContext
    {
        scriptContextTxInfo  :: TxInfo x,
        scriptContextPurpose :: x
    }
    -- deriving (Haskell.Show, Haskell.Eq)

instance Arithmetizable a x => Arithmetizable a (ScriptContext x) where
    arithmetize (ScriptContext txInfo purpose) = do
        txInfo' <- arithmetize txInfo
        purpose' <- arithmetize purpose
        return $ txInfo' ++ purpose'

    restore ctx
        | length ctx == typeSize @a @(ScriptContext x) =
            let txInfo  = restore $ take (typeSize @a @(TxInfo x)) ctx
                purpose = restore $ take (typeSize @a @x) $ drop (typeSize @a @(TxInfo x)) ctx
            in ScriptContext txInfo purpose
        | otherwise = error "restore ScriptContext: wrong number of arguments"

    typeSize = typeSize @a @(TxInfo x) + typeSize @a @x

newtype Value x = Value x

instance Arithmetizable a x => Arithmetizable a (Value x) where
    arithmetize (Value x) = arithmetize x

    restore v
        | length v == typeSize @a @x = Value $ restore v
        | otherwise = error "restore Value: wrong number of arguments"

    typeSize = typeSize @a @x

data TxOut x = TxOut x x x
    deriving (Haskell.Show, Haskell.Eq)

instance Arithmetizable a x => Arithmetizable a (TxOut x) where
    arithmetize (TxOut addr value data') = do
        addr'  <- arithmetize addr
        value' <- arithmetize value
        data'' <- arithmetize data'
        return $ concat [addr', value', data'']

    restore out
        | length out == typeSize @a @(TxOut x) =
            let addr  = restore $ take (typeSize @a @x) out
                value = restore $ take (typeSize @a @x) $ drop (typeSize @a @x) out
                data' = restore $ take (typeSize @a @x) $ drop (typeSize @a @x + typeSize @a @x) out
            in TxOut addr value data'
        | otherwise = error "restore TxOut: wrong number of arguments"

    typeSize = 3 * typeSize @a @x