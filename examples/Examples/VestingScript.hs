{-# LANGUAGE TypeApplications    #-}

module Examples.VestingScript (exampleVesting) where

import           Data.Foldable                               (toList)
import           Prelude                                     (IO, ($), putStrLn, (++), show)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              (writeFileJSON)
import           ZkFold.Symbolic.Arithmetization
import           ZkFold.Symbolic.Cardano.Types
import           ZkFold.Symbolic.Compiler                    (compile)
import           ZkFold.Symbolic.Data.Bool                   (BoolType (..), Bool (..), any)
import           ZkFold.Symbolic.Data.Eq                     (Eq(..))
import           ZkFold.Symbolic.Data.Ord                    (Ord(..))
import           ZkFold.Symbolic.Types                       (Symbolic)

-- | A simple vesting script. The funds can be withdrawn after the vesting time.
-- NOTE: Not all types are implemented yet. So, most fields of the input arguments are mocks.
vestingScript :: forall a . Symbolic a => Datum a -> Redeemer a -> ScriptContext a -> Bool a
vestingScript datum _ ctx =
    let Datum vestAddr vestTime vestValue = datum

        info  = scriptContextTxInfo ctx
        now   = lowerBound $ txInfoValidRange info
        outs  = toList $ txInfoOutputs info

    in now >= vestTime && any (\(TxOut addr val _) -> (addr == vestAddr) && (val == vestValue)) outs

exampleVesting :: IO ()
exampleVesting = do
    let ac   = compile @(Zp BLS12_381_Scalar) (vestingScript @(ArithmeticCircuit (Zp BLS12_381_Scalar))) :: ArithmeticCircuit (Zp BLS12_381_Scalar)
        file = "compiled_scripts/vesting.json"

    putStrLn "\nExample: Vesting script\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: "   ++ show (acSizeM ac)
    writeFileJSON file ac
    putStrLn $ "Script saved: " ++ file