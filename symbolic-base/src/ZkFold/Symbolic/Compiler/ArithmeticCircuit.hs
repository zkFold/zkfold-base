{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        Constraint,
        Var,
        witnessGenerator,
        -- high-level functions
        optimize,
        desugarRanges,
        emptyCircuit,
        idCircuit,
        naturalCircuit,
        inputPayload,
        guessOutput,
        -- low-level functions
        eval,
        eval1,
        exec,
        exec1,
        -- information about the system
        acSizeN,
        acSizeM,
        acSizeR,
        acSystem,
        acValue,
        acPrint,
        -- Variable mapping functions
        hlmap,
        hpmap,
        mapVarArithmeticCircuit,
        -- Arithmetization type fields
        acWitness,
        acInput,
        acOutput,
        -- Testing functions
        checkCircuit,
        checkClosedCircuit,
        isConstantInput
    ) where

import           Control.DeepSeq                                         (NFData)
import           Control.Monad                                           (foldM)
import           Control.Monad.State                                     (execState, runState)
import           Data.Binary                                             (Binary)
import           Data.Foldable                                           (for_)
import           Data.Functor.Rep                                        (Representable (..), mzipRep)
import           Data.Map                                                hiding (drop, foldl, foldr, map, null, splitAt,
                                                                          take)
import qualified Data.Map.Monoidal                                       as M
import qualified Data.Set                                                as S
import           Data.Traversable                                        (for)
import           Data.Tuple                                              (swap)
import           Data.Void                                               (absurd)
import           GHC.Generics                                            (U1 (..), (:*:))
import           Numeric.Natural                                         (Natural)
import           Prelude                                                 hiding (Num (..), drop, length, product,
                                                                          splitAt, sum, take, (!!), (^))
import           Test.QuickCheck                                         (Arbitrary, Property, arbitrary, conjoin,
                                                                          property, withMaxSuccess, (===))
import           Text.Pretty.Simple                                      (pPrint)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate            (evalMonomial, evalPolynomial)
import           ZkFold.Base.Data.HFunctor                               (hmap)
import           ZkFold.Base.Data.Product                                (fstP, sndP)
import           ZkFold.Prelude                                          (length)
import           ZkFold.Symbolic.Class                                   (fromCircuit2F)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance     ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal     (Arithmetic, ArithmeticCircuit (..),
                                                                          Constraint, SysVar (..), Var (..),
                                                                          WitVar (..), acInput, crown, eval, eval1,
                                                                          exec, exec1, hlmap, hpmap, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Optimization
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Var          (toVar)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness      (WitnessF)
import           ZkFold.Symbolic.Data.Combinators                        (expansion)
import           ZkFold.Symbolic.MonadCircuit                            (MonadCircuit (..))

--------------------------------- High-level functions --------------------------------

desugarRange :: (Arithmetic a, MonadCircuit i a w m) => i -> a -> m ()
desugarRange i b
  | b == negate one = return ()
  | otherwise = do
    let bs = binaryExpansion (toConstant b)
    is <- expansion (length bs) i
    case dropWhile ((== one) . fst) (zip bs is) of
      [] -> return ()
      ((_, k0):ds) -> do
        z <- newAssigned (one - ($ k0))
        ge <- foldM (\j (c, k) -> newAssigned $ forceGE j c k) z ds
        constraint (($ ge) - one)
  where forceGE j c k
          | c == zero = ($ j) * (one - ($ k))
          | otherwise = one + ($ k) * (($ j) - one)

-- | Desugars range constraints into polynomial constraints
desugarRanges ::
  (Arithmetic a, Binary a, Binary (Rep p), Binary (Rep i), Ord (Rep i)) =>
  ArithmeticCircuit a p i o -> ArithmeticCircuit a p i o
desugarRanges c =
  let r' = flip execState c {acOutput = U1} . traverse (uncurry desugarRange) $ [(toVar v, k) | (k, s) <- M.toList (acRange c), v <- S.toList s]
   in r' { acRange = mempty, acOutput = acOutput c }

emptyCircuit :: ArithmeticCircuit a p i U1
emptyCircuit = ArithmeticCircuit empty M.empty empty empty U1

-- | Given a natural transformation
-- from payload @p@ and input @i@ to output @o@,
-- returns a corresponding arithmetic circuit
-- where outputs computing the payload are unconstrained.
naturalCircuit ::
  ( Arithmetic a, Representable p, Representable i, Traversable o
  , Binary a, Binary (Rep p), Binary (Rep i), Ord (Rep i)) =>
  (forall x. p x -> i x -> o x) -> ArithmeticCircuit a p i o
naturalCircuit f = uncurry crown $ swap $ flip runState emptyCircuit $
  for (f (tabulate Left) (tabulate Right)) $
    either (unconstrained . pure . WExVar) (return . toVar . InVar)

-- | Identity circuit which returns its input @i@ and doesn't use the payload.
idCircuit :: (Representable i, Semiring a) => ArithmeticCircuit a p i i
idCircuit = emptyCircuit { acOutput = acInput }

-- | Payload of an input to arithmetic circuit.
-- To be used as an argument to 'compileWith'.
inputPayload ::
  (Representable p, Representable i) =>
  (forall x. p x -> i x -> o x) -> o (WitnessF a (WitVar p i))
inputPayload f =
  f (tabulate $ pure . WExVar) (tabulate $ pure . WSysVar . InVar)

guessOutput ::
  (Arithmetic a, Binary a, Binary (Rep p), Binary (Rep i), Binary (Rep o)) =>
  (Ord (Rep i), Ord (Rep o), NFData (Rep i), NFData (Rep o)) =>
  (Representable i, Representable o, Foldable o) =>
  ArithmeticCircuit a p i o -> ArithmeticCircuit a p (i :*: o) o
guessOutput c = fromCircuit2F (hlmap fstP c) (hmap sndP idCircuit) $ \o o' -> do
  for_ (mzipRep o o') $ \(i, j) -> constraint (\x -> x i - x j)
  return o

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a p i o -> Natural
acSizeN = length . acSystem

-- | Calculates the number of variables in the system.
acSizeM :: ArithmeticCircuit a p i o -> Natural
acSizeM = length . acWitness

-- | Calculates the number of range lookups in the system.
acSizeR :: ArithmeticCircuit a p i o -> Natural
acSizeR = sum . map length . M.elems . acRange

acValue :: (Arithmetic a, Functor o) => ArithmeticCircuit a U1 U1 o -> o a
acValue = exec

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint :: forall a o.
  (Arithmetic a, Show a, Show (o (Var a U1)), Show (o a), Functor o) =>
  ArithmeticCircuit a U1 U1 o -> IO ()
acPrint ac = do
    let m = elems (acSystem ac)
        w = witnessGenerator @a ac U1 U1
        v = acValue ac
        o = acOutput ac
    putStr "System size: "
    pPrint $ acSizeN ac
    putStr "Variable size: "
    pPrint $ acSizeM ac
    putStr "Matrices: "
    pPrint m
    putStr "Witness: "
    pPrint w
    putStr "Output: "
    pPrint o
    putStr "Value: "
    pPrint v

---------------------------------- Testing -------------------------------------

isConstantInput :: forall a p i o.
  ( Arithmetic a, Show a, Representable p, Representable i
  , Show (p a), Show (i a), Arbitrary (p a), Arbitrary (i a)
  ) => ArithmeticCircuit a p i o -> Property
isConstantInput c = property $ \x y p -> witnessGenerator @a c p x === witnessGenerator c p y

checkClosedCircuit
    :: forall a o
     . Arithmetic a
    => Show a
    => ArithmeticCircuit a U1 U1 o
    -> Property
checkClosedCircuit c = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem c) ]
    where
        w = witnessGenerator @a c U1 U1
        testPoly p = evalPolynomial evalMonomial varF p === zero
        varF (NewVar v) = w ! v
        varF (InVar v)  = absurd v

checkCircuit
    :: forall a p i o
     . Arbitrary (p a)
    => Arbitrary (i a)
    => Arithmetic a
    => Show a
    => Representable p
    => Representable i
    => ArithmeticCircuit a p i o
    -> Property
checkCircuit c = conjoin [ property (testPoly p) | p <- elems (acSystem c) ]
    where
        testPoly p = do
            ins <- arbitrary
            pls <- arbitrary
            let w = witnessGenerator @a c pls ins
                varF (NewVar v) = w ! v
                varF (InVar v)  = index ins v
            return $ evalPolynomial evalMonomial varF p === zero
