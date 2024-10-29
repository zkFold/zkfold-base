{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
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
import           Data.Functor.Rep                           (Rep, Representable)
import           Data.Ord                                   (Ord)
import           Data.Proxy                                 (Proxy (..))
import           Data.Traversable                           (for)
import           GHC.Generics                               (Par1 (Par1))
import           Prelude                                    (FilePath, IO, Show (..), Traversable, putStrLn, return,
                                                             type (~), ($), (++))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                             (writeFileJSON)
import           ZkFold.Symbolic.Class                      (Arithmetic, Symbolic (..), fromCircuit2F)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Data.Bool                  (Bool (Bool))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Input
import           ZkFold.Symbolic.MonadCircuit               (MonadCircuit (..), newConstrained)

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
    forall a c f s l .
    ( c ~ ArithmeticCircuit a l
    , SymbolicInput f
    , Context f ~ c
    , Support f ~ s
    , SymbolicData s
    , Support s ~ Proxy c
    , Layout s ~ l
    , Representable l
    , Ord (Rep l)
    , Symbolic c
    ) => f -> c (Layout f)
solder f = fromCircuit2F p1 p2 solve
    where
        p1 = pieces f $ acInput @f
        Bool p2 = isValid @s $ acInput @f

        solve :: MonadCircuit i (BaseField c) m => Layout f i -> Par1 i -> m (Layout f i)
        solve l (Par1 r) = do
            constraint (\x -> one - x r)
            return l

-- | Compiles function `f` into an arithmetic circuit with all outputs equal to 1.
compileForceOne ::
    forall a c f s l y .
    ( c ~ ArithmeticCircuit a l
    , Arithmetic a
    , Binary a
    , SymbolicInput f
    , Support f ~ s
    , SymbolicData s
    , Context s ~ c
    , Support s ~ Proxy c
    , Layout s ~ l
    , Representable l
    , Binary (Rep l)
    , Ord (Rep l)
    , SymbolicData y
    , Context y ~ c
    , Support y ~ Proxy c
    , Layout f ~ Layout y
    , Traversable (Layout y)
    ) => f -> y
compileForceOne = restore . const . optimize . forceOne . solder @a

-- | Compiles function `f` into an arithmetic circuit.
compile ::
    forall a c f s l y .
    ( c ~ ArithmeticCircuit a l
    , SymbolicInput f
    , Context f ~ c
    , Support f ~ s
    , SymbolicData s
    , Support s ~ Proxy c
    , Layout s ~ l
    , Representable l
    , Ord (Rep l)
    , SymbolicData y
    , Context y ~ c
    , Support y ~ Proxy c
    , Layout f ~ Layout y
    , Symbolic c
    ) => f -> y
compile = restore . const . optimize . solder @a

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO ::
    forall a c f s l .
    ( c ~ ArithmeticCircuit a l
    , FromJSON a
    , ToJSON a
    , SymbolicInput f
    , Context f ~ c
    , Support f ~ s
    , ToJSON (Layout f (Var a l))
    , SymbolicData s
    , Support s ~ Proxy c
    , Layout s ~ l
    , Representable l
    , Ord (Rep l)
    , FromJSON (Rep l)
    , ToJSON (Rep l)
    , Symbolic c
    ) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = optimize (solder @a f) :: c (Layout f)

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
