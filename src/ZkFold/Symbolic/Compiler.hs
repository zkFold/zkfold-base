{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.Arithmetizable,
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile',
    compile,
    compileIO
) where

import           Data.Aeson                                                (ToJSON)
import           Data.Foldable                                             (fold)
import           Prelude                                                   (FilePath, IO, Show (..), putStrLn, ($),
                                                                            (++), type (~))

import           ZkFold.Prelude                                            (replicateA, writeFileJSON)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Compiler.Arithmetizable

import ZkFold.Base.Algebra.Basic.Class

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

compile'
  :: ( Arithmetic a
     , Tensorial (ArithmeticCircuit a) t
     , y ~ OutputSpace (ArithmeticCircuit a) t
     )
  => t -> y (ArithmeticCircuit a)
compile' = evalT (\_ -> circuit input)

-- | Arithmetizes an argument by feeding an appropriate amount of inputs.
solder :: forall a f . Arithmetizable a f => f -> [ArithmeticCircuit a]
solder f = arithmetize f $ circuits $ replicateA (inputSize @a @f) input

-- | Compiles function `f` into an arithmetic circuit.
compile :: forall a f y . (Arithmetizable a f, SymbolicData a y) => f -> y
compile f = restore @a (solder f)

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO :: forall a f . (ToJSON a, Arithmetizable a f) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = fold (solder f) :: ArithmeticCircuit a

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
