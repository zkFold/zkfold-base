{-# LANGUAGE TypeApplications    #-}

module Examples.VestingScript (exampleVesting) where

import           Prelude                                     (IO, Show (..), ($), (++), putStrLn)

import           ZkFold.Cardano.Types
import           ZkFold.Crypto.Algebra.Basic.Field           (Zp)
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean (..), Bool (..), any)
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq(..))
import           ZkFold.Crypto.Data.Ord                      (GeneralizedOrd(..))
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS

import           Tests.Utility.Types                         (Symbolic, R, SmallField)

vestingScript :: forall a . Symbolic a => Datum a -> Redeemer a -> ScriptContext a -> Bool a
vestingScript datum _ ctx =
    let Datum vestAddr vestTime vestValue = datum

        info  = scriptContextTxInfo ctx
        now   = lowerBound $ txInfoValidRange info
        outs  = txInfoOutputs info

    in now >= vestTime && any (\(TxOut addr val _) -> (addr == vestAddr) && (val == vestValue)) outs

exampleVesting :: IO ()
exampleVesting = do
    let Bool r = compile @(Zp SmallField) (vestingScript @R) :: Bool R

    putStrLn "\nStarting Vesting Script test...\n"

    putStrLn "Vesting Script:"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (r1csSizeN r)
    putStrLn $ "Number of variables: " ++ show (r1csSizeM r)