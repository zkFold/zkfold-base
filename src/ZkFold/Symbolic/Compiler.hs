{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.Arithmetizable,
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO
) where

import           Data.Aeson                                          (ToJSON)
import           Data.Function                                       (const, (.))
import           Prelude                                             (FilePath, IO, Monoid (mempty), Show (..),
                                                                      putStrLn, type (~), ($), (++))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                             (Vector, unsafeToVector)
import           ZkFold.Prelude                                      (writeFileJSON)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (acInput)
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
solder ::
    forall a f .
    ( SymbolicData a f
    , SymbolicData a (Support a f)
    , Support a (Support a f) ~ ()
    , KnownNat (TypeSize a (Support a f))
    ) => f -> ArithmeticCircuit a (Vector (TypeSize a f))
solder f = pieces f (restore @a @(Support a f) $ const inputC)
    where
        inputList = [1..(typeSize @a @(Support a f))]
        inputC = withOutputs (mempty { acInput = inputList }) (unsafeToVector inputList)

-- | Compiles function `f` into an arithmetic circuit.
compile ::
    forall a f y .
    ( SymbolicData a f
    , SymbolicData a (Support a f)
    , Support a (Support a f) ~ ()
    , KnownNat (TypeSize a (Support a f))
    , SymbolicData a y
    , Support a y ~ ()
    , TypeSize a f ~ TypeSize a y
    ) => f -> y
compile = restore @a . const . optimize . solder @a

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO ::
    forall a f .
    ( ToJSON a
    , SymbolicData a f
    , SymbolicData a (Support a f)
    , Support a (Support a f) ~ ()
    , KnownNat (TypeSize a (Support a f))
    ) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a f) :: ArithmeticCircuit a (Vector (TypeSize a f))

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
