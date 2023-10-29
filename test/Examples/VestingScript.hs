{-# LANGUAGE TypeApplications    #-}

module Examples.VestingScript (exampleVesting) where

import           Data.Foldable                   (toList)
import           Prelude                         (IO, Show (..), ($), (++), putStrLn)

import           ZkFold.Cardano.Types
import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Arithmetization
import           ZkFold.Symbolic.Data.Bool       (BoolType (..), Bool (..), any)
import           ZkFold.Symbolic.Data.Eq         (Eq(..))
import           ZkFold.Symbolic.Data.Ord        (Ord(..))
import           ZkFold.Symbolic.Types           (Symbolic, R, SmallField)

vestingScript :: forall a . Symbolic a => Datum a -> Redeemer a -> ScriptContext a -> Bool a
vestingScript datum _ ctx =
    let Datum vestAddr vestTime vestValue = datum

        info  = scriptContextTxInfo ctx
        now   = lowerBound $ txInfoValidRange info
        outs  = toList $ txInfoOutputs info

    in now >= vestTime && any (\(TxOut addr val _) -> (addr == vestAddr) && (val == vestValue)) outs

exampleVesting :: IO ()
exampleVesting = do
    let Bool r = compile @(Zp SmallField) (vestingScript @R) :: Bool R

    putStrLn "\nStarting Vesting Script test...\n"

    putStrLn "Vesting Script:"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (acSizeN r)
    putStrLn $ "Number of variables: " ++ show (acSizeM r)