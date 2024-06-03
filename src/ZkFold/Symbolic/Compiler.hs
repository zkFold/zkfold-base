{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.Arithmetizable,
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO
) where

import           Data.Aeson                                                (ToJSON)
import           Prelude                                                   (FilePath, IO, Show (..), putStrLn, ($),
                                                                            (++), (<$>))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (replicateA, writeFileJSON)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (ArithmeticCircuit (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
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

-- | Arithmetizes an argument by feeding an appropriate amount of inputs.
solder :: forall a i o f . Arithmetizable a i o f => f -> ArithmeticCircuit o a
solder f = arithmetize f inputC
    where
        inputC :: ArithmeticCircuit i a
        inputC = circuitN $ Vector <$> replicateA (value @i) input

-- | Compiles function `f` into an arithmetic circuit.
compile :: forall a i o f y . (Arithmetizable a i o f, SymbolicData a o y) => f -> y
compile f = restore @a c o
    where
        ArithmeticCircuit c o = optimize $ (solder @a @i @o) f

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO :: forall a i o f . (ToJSON a, Arithmetizable a i o f) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a @i @o f) :: ArithmeticCircuit o a

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
