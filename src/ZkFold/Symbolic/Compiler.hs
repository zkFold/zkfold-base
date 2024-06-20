{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.Arithmetizable,
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO
) where

import           Data.Aeson                                                (ToJSON)
import           Prelude                                                   (FilePath, IO, Show (..), putStrLn, type (~),
                                                                            ($), (++), (<$>))

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
solder :: forall a f . (Arithmetizable a f, KnownNat (InputSize a f)) => f -> ArithmeticCircuit (OutputSize a f) a
solder f = arithmetize f inputC
    where
        inputC :: ArithmeticCircuit (InputSize a f) a
        inputC = circuitN $ Vector <$> replicateA (value @(InputSize a f)) input

-- | Compiles function `f` into an arithmetic circuit.
compile 
    :: forall a f y 
    .  Arithmetizable a f 
    => SymbolicData a y
    => KnownNat (InputSize a f)
    => OutputSize a f ~ TypeSize a y 
    => f -> y
compile f = restore @a c o
    where
        ArithmeticCircuit c o = optimize $ (solder @a) f

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO :: forall a f . (ToJSON a, Arithmetizable a f, KnownNat (InputSize a f)) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a f) :: ArithmeticCircuit (OutputSize a f) a

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
