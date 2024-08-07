{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO,
    compileForceOne
) where

import           Data.Aeson                                             (ToJSON)
import           Data.Eq                                                (Eq)
import           Data.Function                                          (const, (.))
import           Prelude                                                (FilePath, IO, Monoid (mempty), Show (..),
                                                                         putStrLn, type (~), ($), (++))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                                (Vector)
import           ZkFold.Prelude                                         (writeFileJSON)
import           ZkFold.Symbolic.Class                                  (Arithmetic)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (forceOne)
import           ZkFold.Symbolic.Data.Class

{-
    ZkFold Symbolic compiler module dependency order:
    1. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
    2. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
    3. ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
    4. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators
    5. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance
    6. ZkFold.Symbolic.Compiler.ArithmeticCircuit
    7. ZkFold.Symbolic.Compiler
-}

-- | Arithmetizes an argument by feeding an appropriate amount of inputs.
solder ::
    forall a c f .
    ( Eq a
    , MultiplicativeMonoid a
    , c ~ ArithmeticCircuit a (Vector (TypeSize c (Support c f)))
    , SymbolicData c f
    , SymbolicData c (Support c f)
    , Support c (Support c f) ~ ()
    , KnownNat (TypeSize c (Support c f))
    ) => f -> c (Vector (TypeSize c f))
solder f = pieces f (restore @c @(Support c f) $ const inputC)
    where
        inputC = mempty { acOutput = acInput }

-- | Compiles function `f` into an arithmetic circuit with all outputs equal to 1.
compileForceOne ::
    forall a c f y .
    ( c ~ ArithmeticCircuit a (Vector (TypeSize c (Support c f)))
    , Arithmetic a
    , SymbolicData c f
    , SymbolicData c (Support c f)
    , Support c (Support c f) ~ ()
    , KnownNat (TypeSize c (Support c f))
    , SymbolicData c y
    , Support c y ~ ()
    , TypeSize c f ~ TypeSize c y
    ) => f -> y
compileForceOne = restore @c . const . optimize . forceOne . solder @a

-- | Compiles function `f` into an arithmetic circuit.
compile ::
    forall a c f y .
    ( Eq a
    , MultiplicativeMonoid a
    , c ~ ArithmeticCircuit a (Vector (TypeSize c (Support c f)))
    , SymbolicData c f
    , SymbolicData c (Support c f)
    , Support c (Support c f) ~ ()
    , KnownNat (TypeSize c (Support c f))
    , SymbolicData c y
    , Support c y ~ ()
    , TypeSize c f ~ TypeSize c y
    ) => f -> y
compile = restore @c . const . optimize . solder @a

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO ::
    forall a c f .
    ( Eq a
    , MultiplicativeMonoid a
    , c ~ ArithmeticCircuit a (Vector (TypeSize c (Support c f)))
    , ToJSON a
    , SymbolicData c f
    , SymbolicData c (Support c f)
    , Support c (Support c f) ~ ()
    , KnownNat (TypeSize c (Support c f))
    ) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a f) :: c (Vector (TypeSize c f))

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
