{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.Arithmetizable,
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO
) where

import           Control.Monad.State                        (execState)
import           Data.Aeson                                 (ToJSON)
import           Prelude                                    (FilePath, IO, Show (..), mempty, putStrLn, ($), (++))

import           ZkFold.Prelude                             (writeFileJSON)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Compiler.Arithmetizable

{-
    ZkFold Symbolic compiler module dependency order:
    1. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
    2. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
    3. ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
    4. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators
    5. ZkFold.Symbolic.Compiler.Arithmetizable
    6. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance
    7. ZkFold.Symbolic.Compiler.ArithmeticCircuit
    8. ZkFold.Symbolic.Compiler
-}

-- | Compiles function `f` into an arithmetic circuit.
compile :: forall a f y . (Arithmetizable a f, Arithmetizable a y) => f -> y
compile f = restore @a $ circuits (arithmetize f)

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO :: forall a f . (ToJSON a, Arithmetizable a f) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = execState (arithmetize f) mempty :: ArithmeticCircuit a

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
