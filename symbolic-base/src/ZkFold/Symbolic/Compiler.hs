{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO,
    compileForceOne,
    solder,
) where

import           Data.Aeson                                 (FromJSON, ToJSON)
import           Data.Binary                                (Binary)
import           Data.Function                              (const, (.))
import           Data.Functor                               (($>))
import           Data.Proxy                                 (Proxy)
import           Data.Traversable                           (for)
import           Prelude                                    (FilePath, IO, Monoid (mempty), Show (..), Traversable,
                                                             putStrLn, type (~), ($), (++))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Prelude                             (writeFileJSON)
import           ZkFold.Symbolic.Class                      (Arithmetic, Symbolic (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.MonadCircuit               (MonadCircuit (..))

{-
    ZkFold Symbolic compiler module dependency order:
    1. ZkFold.Symbolic.Compiler.ArithmeticCircuit.MerkleHash
    2. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
    3. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
    4. ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance
    5. ZkFold.Symbolic.Compiler.ArithmeticCircuit
    6. ZkFold.Symbolic.Compiler
-}

forceOne :: (Symbolic c, Traversable f) => c f -> c f
forceOne r = fromCircuitF r (\fi -> for fi $ \i -> constraint (\x -> x i - one) $> i)

-- | Arithmetizes an argument by feeding an appropriate amount of inputs.
solder ::
    forall a c f ni .
    ( KnownNat ni
    , c ~ ArithmeticCircuit a (Vector ni)
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    , Layout f ~ Vector (TypeSize f)
    , Layout (Support f) ~ Vector ni
    ) => f -> c (Vector (TypeSize f))
solder f = pieces f (restore @(Support f) $ const inputC)
    where
        inputC = mempty { acOutput = acInput }

-- | Compiles function `f` into an arithmetic circuit with all outputs equal to 1.
compileForceOne ::
    forall a c f y ni .
    ( KnownNat ni
    , c ~ ArithmeticCircuit a (Vector ni)
    , Arithmetic a
    , Binary a
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    , SymbolicData y
    , Context y ~ c
    , Support y ~ Proxy c
    , TypeSize f ~ TypeSize y
    , Layout f ~ Vector (TypeSize y)
    , Layout y ~ Vector (TypeSize y)
    , Layout (Support f) ~ Vector ni
    ) => f -> y
compileForceOne = restore . const . optimize . forceOne . solder @a

-- | Compiles function `f` into an arithmetic circuit.
compile ::
    forall a c f y ni .
    ( KnownNat ni
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
    , Layout f ~ Vector (TypeSize y)
    , Layout y ~ Vector (TypeSize y)
    , Layout (Support f) ~ Vector ni
    ) => f -> y
compile = restore . const . optimize . solder @a

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO ::
    forall a c f ni .
    ( KnownNat ni
    , c ~ ArithmeticCircuit a (Vector ni)
    , FromJSON a
    , ToJSON a
    , SymbolicData f
    , Context f ~ c
    , SymbolicData (Support f)
    , Context (Support f) ~ c
    , Support (Support f) ~ Proxy c
    , Layout f ~ Vector (TypeSize f)
    , Layout (Support f) ~ Vector ni
    ) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a f) :: c (Vector (TypeSize f))

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
