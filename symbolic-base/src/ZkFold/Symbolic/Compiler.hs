{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Compiler (
    module ZkFold.Symbolic.Compiler.ArithmeticCircuit,
    compile,
    compileIO,
    compileWith
) where

import           Data.Aeson                                 (FromJSON, ToJSON, ToJSONKey)
import           Data.Binary                                (Binary)
import           Data.Function                              (const, id, (.))
import           Data.Functor.Rep                           (Rep, Representable)
import           Data.Ord                                   (Ord)
import           Data.Proxy                                 (Proxy (..))
import           Data.Tuple                                 (fst, snd)
import           GHC.Generics                               (Par1 (Par1), U1 (..))
import           Prelude                                    (FilePath, IO, Show (..), putStrLn, return,
                                                             type (~), ($), (++))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                             (writeFileJSON)
import           ZkFold.Symbolic.Class                      (Arithmetic, Symbolic (..), fromCircuit2F)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Data.Bool                  (Bool (Bool))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Input
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

-- | A constraint defining what it means
-- for function of type @f@ to be compilable.
type CompilesWith c s f =
  ( SymbolicData f, Context f ~ c, Support f ~ s
  , SymbolicInput s, Context s ~ c, Symbolic c)

-- | A constraint defining what it means
-- for data of type @y@ to be properly restorable.
type RestoresFrom c y =
  (SymbolicData y, Context y ~ c, Support y ~ Proxy c, Payload y ~ U1)

compileInternal ::
  (CompilesWith c0 s f, RestoresFrom c1 y, c1 ~ ArithmeticCircuit a p i) =>
  (c0 (Layout f) -> c1 (Layout y)) ->
  c0 (Layout s) -> Payload s (WitnessField c0) -> f -> y
compileInternal opts sLayout sPayload f =
  restore . const . (,U1) . optimize . opts $
    fromCircuit2F (arithmetize f input) b $
      \r (Par1 i) -> do
        constraint (\x -> one - x i)
        return r
  where
    Bool b = isValid input
    input = restore $ const (sLayout, sPayload)

-- | @compileWith opts inputT@ compiles a function @f@ into an optimized
-- arithmetic circuit packed inside a suitable 'SymbolicData'.
compileWith ::
  forall a y p i q j s f c0 c1.
  ( CompilesWith c0 s f, c0 ~ ArithmeticCircuit a p i
  , Representable p, Representable i
  , RestoresFrom c1 y, c1 ~ ArithmeticCircuit a q j
  , Binary a, Binary (Rep p), Binary (Rep i), Ord (Rep i)) =>
  -- | Circuit transformation to apply before optimization.
  (c0 (Layout f) -> c1 (Layout y)) ->
  -- | An algorithm to prepare support argument from the circuit input.
  (forall x. p x -> i x -> (Payload s x, Layout s x)) ->
  -- | Function to compile.
  f -> y
compileWith outputTransform inputTransform =
  compileInternal outputTransform
    (naturalCircuit $ \p i -> snd (inputTransform p i))
    (inputPayload $ \p i -> fst (inputTransform p i))

-- | @compile f@ compiles a function @f@ into an optimized arithmetic circuit
-- packed inside a suitable 'SymbolicData'.
compile :: forall a y f c s.
  ( CompilesWith c s f, RestoresFrom c y, Layout y ~ Layout f
  , c ~ ArithmeticCircuit a (Payload s) (Layout s))
  => f -> y
compile = compileInternal id idCircuit (inputPayload const)

-- | Compiles a function `f` into an arithmetic circuit. Writes the result to a file.
compileIO ::
  forall a c p f s l .
  ( c ~ ArithmeticCircuit a p l
  , FromJSON a
  , ToJSON a
  , ToJSONKey a
  , SymbolicData f
  , Context f ~ c
  , Support f ~ s
  , ToJSON (Layout f (Var a l))
  , SymbolicInput s
  , Context s ~ c
  , Layout s ~ l
  , Payload s ~ p
  , FromJSON (Rep l)
  , ToJSON (Rep l)
  , Arithmetic a, Binary a, Binary (Rep p)
  ) => FilePath -> f -> IO ()
compileIO scriptFile f = do
    let ac = compile f :: c (Layout f)

    putStrLn "\nCompiling the script...\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: " ++ show (acSizeM ac)
    writeFileJSON scriptFile ac
    putStrLn $ "Script saved: " ++ scriptFile
