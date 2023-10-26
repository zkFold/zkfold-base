module ZkFold.Cardano.Types where

import           Prelude                            (($), concat, return, error, (++), fst, snd)
import qualified Prelude                            as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Protocol.Arithmetization.R1CS (Arithmetizable(..))

data Datum x = Datum x x x

instance Arithmetizable a x => Arithmetizable a (Datum x) where
    arithmetize (Datum addr vTime ada) = do
        addrAC  <- arithmetize addr
        vTimeAC <- arithmetize vTime
        adaAC   <- arithmetize ada
        return $ concat [addrAC, vTimeAC, adaAC]

    restore [addrAC, vTimeAC, adaAC] = Datum (restore [addrAC]) (restore [vTimeAC]) (restore [adaAC])
    restore _ = error "restore Datum: wrong number of arguments"

    typeSize = 3

data Redeemer x = Redeemer

instance Arithmetizable a x => Arithmetizable a (Redeemer x) where
    arithmetize Redeemer = return [one]

    restore [] = Redeemer
    restore _  = error "restore Redeemer: wrong number of arguments"

    typeSize = 0

data TxInfo x = TxInfo
    {
        txInfoInputs          :: [x],
        txInfoReferenceInputs :: [x],
        txInfoOutputs         :: [TxOut x],
        txInfoFee             :: x,
        txInfoForge           :: x,
        txInfoDCert           :: [x],
        txInfoWdrl            :: x,
        txInfoValidRange      :: (x, x),
        txInfoSignatories     :: [x],
        txInfoData            :: [x],
        txInfoId              :: x
    }
    deriving (Haskell.Show, Haskell.Eq)

instance Arithmetizable a x => Arithmetizable a (TxInfo x) where
    arithmetize (TxInfo inputs referenceInputs outputs fee forge dCert wdrl validRange signatories data' id) = do
        inputs'          <- arithmetize inputs
        referenceInputs' <- arithmetize referenceInputs
        outputs'         <- arithmetize outputs
        fee'             <- arithmetize fee
        forge'           <- arithmetize forge
        dCert'           <- arithmetize dCert
        wdrl'            <- arithmetize wdrl
        validRange'      <- arithmetize validRange
        signatories'     <- arithmetize signatories
        data''           <- arithmetize data'
        id'              <- arithmetize id
        return $ concat [inputs', referenceInputs', outputs', fee', forge', dCert', wdrl', validRange', signatories', data'', id']

    restore [inputs', referenceInputs', outputs', fee', forge', dCert', wdrl', validRange', signatories', data'', id'] = TxInfo
        (restore [inputs'])
        (restore [referenceInputs'])
        (restore [outputs'])
        (restore [fee'])
        (restore [forge'])
        (restore [dCert'])
        (restore [wdrl'])
        (restore [validRange'])
        (restore [signatories'])
        (restore [data''])
        (restore [id'])
    restore _ = error "restore TxInfo: wrong number of arguments"

    typeSize = 0

lowerBound :: (x, x) -> x
lowerBound = fst

upperBound :: (x, x) -> x
upperBound = snd

data ScriptContext x = ScriptContext
    {
        scriptContextTxInfo  :: TxInfo x,
        scriptContextPurpose :: x
    }
    deriving (Haskell.Show, Haskell.Eq)

instance Arithmetizable a x => Arithmetizable a (ScriptContext x) where
    arithmetize (ScriptContext txInfo purpose) = do
        txInfo' <- arithmetize txInfo
        purpose' <- arithmetize purpose
        return $ txInfo' ++ purpose'

    restore [txInfo', purpose'] = ScriptContext
        (restore [txInfo'])
        (restore [purpose'])
    restore _ = error "restore ScriptContext: wrong number of arguments"

    typeSize = 0

newtype Value x = Value x

instance Arithmetizable a x => Arithmetizable a (Value x) where
    arithmetize (Value x) = arithmetize x

    restore [x] = Value $ restore [x]
    restore _   = error "restore Value: wrong number of arguments"

    typeSize = 1

data TxOut x = TxOut x x x
    deriving (Haskell.Show, Haskell.Eq)

instance Arithmetizable a x => Arithmetizable a (TxOut x) where
    arithmetize (TxOut addr value data') = do
        addr'  <- arithmetize addr
        value' <- arithmetize value
        data'' <- arithmetize data'
        return $ concat [addr', value', data'']

    restore [addr', value', data''] = TxOut (restore [addr']) (restore [value']) (restore [data''])
    restore _ = error "restore TxOut: wrong number of arguments"

    typeSize = 0
