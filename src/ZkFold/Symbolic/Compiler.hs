{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Compiler where

import           Control.Monad.State             (evalState)
import           Data.Aeson                      (ToJSON)
import           Prelude                         (IO, Show (..), FilePath, ($), (++), putStrLn, mempty)

import           ZkFold.Prelude                  (writeFileJSON)
import           ZkFold.Symbolic.Arithmetization
import           ZkFold.Symbolic.Data.Bool       (Bool (..))

-- | Compiles function `f` into an arithmetic circuit.
compile :: forall a f y . (Arithmetizable a f, Arithmetizable a y) => f -> y
compile f = restore @a $ evalState (arithmetize f) mempty

-- | Compiles a function `f` that returns `Bool a` into an arithmetic circuit. Writes the result to a file.
compileIO :: forall a f . (ToJSON a, Arithmetizable a f) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let Bool ac = compile @a f :: Bool (ArithmeticCircuit a)

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile