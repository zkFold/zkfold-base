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
import           Data.Proxy                                             (Proxy)
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
    forall a c f ni .
    ( Eq a
    , MultiplicativeMonoid a
    , KnownNat ni
    , ni ~ TypeSize (Support f)
    , c ~ ArithmeticCircuit a (Vector ni)
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    ) => f -> c (Vector (TypeSize f))
solder f = pieces f (restore @(Support f) $ const inputC)
    where
        inputC = mempty { acOutput = acInput }

compileForceOne ::
    forall a c f y ni .
    ( KnownNat ni
    , ni ~ TypeSize (Support f)
    , c ~ ArithmeticCircuit a (Vector ni)
    , Arithmetic a
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    , SymbolicData y
    , Context y ~ c
    , Support y ~ Proxy c
    , TypeSize f ~ TypeSize y
    ) => f -> y
compileForceOne = restore . const . optimize . forceOne . solder @a

-- | Compiles function `f` into an arithmetic circuit.
compile ::
    forall a c f y ni .
    ( Eq a
    , MultiplicativeMonoid a
    , KnownNat ni
    , ni ~ TypeSize (Support f)
    , c ~ ArithmeticCircuit a (Vector ni)
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    , SymbolicData y
    , Context y ~ c
    , Support y ~ Proxy c
    , TypeSize f ~ TypeSize y
    ) => f -> y
compile = restore . const . optimize . solder @a

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO ::
    forall a c f ni .
    ( Eq a
    , MultiplicativeMonoid a
    , KnownNat ni
    , ni ~ TypeSize (Support f)
    , c ~ ArithmeticCircuit a (Vector ni)
    , ToJSON a
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    ) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a f) :: c (Vector (TypeSize f))

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
