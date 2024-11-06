module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        ArithmeticCircuitTest(..),
        Constraint,
        Var,
        witnessGenerator,
        -- high-level functions
        optimize,
        desugarRanges,
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
        mapVarArithmeticCircuit,
        -- Arithmetization type fields
        acWitness,
        acInput,
        acOutput,
        acRange,
        -- Testing functions
        checkCircuit,
        checkClosedCircuit
    ) where

import           Control.Monad                                       (foldM)
import           Control.Monad.State                                 (execState)
import           Data.Binary                                         (Binary)
import           Data.Functor.Rep                                    (Representable (..))
import           Data.Map                                            hiding (drop, foldl, foldr, map, null, splitAt,
                                                                      take)
import           Data.Void                                           (absurd)
import           GHC.Generics                                        (U1 (..))
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))
import           Test.QuickCheck                                     (Arbitrary, Property, arbitrary, conjoin, property,
                                                                      withMaxSuccess, (===))
import           Text.Pretty.Simple                                  (pPrint)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (evalMonomial, evalPolynomial)
import           ZkFold.Prelude                                      (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Constraint,
                                                                      SysVar (..), Var (..), acInput, eval, eval1, exec,
                                                                      exec1, hlmap, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
import           ZkFold.Symbolic.Data.Combinators                    (expansion)
import           ZkFold.Symbolic.MonadCircuit                        (MonadCircuit (..))
import ZkFold.Symbolic.Lookup
import qualified Data.Set as S

--------------------------------- High-level functions --------------------------------

-- | Optimizes the constraint system.
--
-- TODO: Implement nontrivial optimizations.
optimize :: ArithmeticCircuit a l i o -> ArithmeticCircuit a l i o
optimize = id

desugarRange :: (Arithmetic a, MonadCircuit i a m) => i -> a -> m ()
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
  (Arithmetic a, Binary a, Binary (Rep i), Ord (Rep i), Representable i) =>
  ArithmeticCircuit a l i o -> ArithmeticCircuit a l i o
desugarRanges c =
  let r' = flip execState c {acOutput = U1} . traverse (uncurry desugarRange) $ [(SysVar v, fromConstant k) | (Range k,s) <- toList (acRange c), v <- S.toList s]
   in r' { acLookup = mempty, acOutput = acOutput c }

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a l i o -> Natural
acSizeN = length . acSystem

-- | Calculates the number of variables in the system.
acSizeM :: ArithmeticCircuit a l i o -> Natural
acSizeM = length . acWitness
        
-- | Calculates the number of lookups in the system.
acSizeL :: ArithmeticCircuit a l i o -> Natural
acSizeL = length . acLookup

-- | Calculates the number of lookups in the system.
acSizeR :: ArithmeticCircuit a l i o -> Natural
acSizeR = length . acRange

-- | Calculates the number of lookups in the system.
acRange :: ArithmeticCircuit a l i o -> Map Lookup (S.Set (SysVar i))
acRange = filterWithKey 
    (\x _ -> case x of
        Range _ -> True
        _       -> False) . acLookup

acValue :: Functor o => ArithmeticCircuit a l U1 o -> o a
acValue r = eval r U1

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint :: (Show a, Show (o (Var a U1)), Show (o a), Functor o) => ArithmeticCircuit a l U1 o -> IO ()
acPrint ac = do
    let m = elems (acSystem ac)
        w = witnessGenerator ac U1
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

checkClosedCircuit
    :: forall a n l
     . Arithmetic a
    => Show a
    => ArithmeticCircuit a l U1 n
    -> Property
checkClosedCircuit c = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem c) ]
    where
        w = witnessGenerator c U1
        testPoly p = evalPolynomial evalMonomial varF p === zero
        varF (NewVar v) = w ! v
        varF (InVar v)  = absurd v

checkCircuit
    :: Arbitrary (i a)
    => Arithmetic a
    => Show a
    => Representable i
    => ArithmeticCircuit a l i n
    -> Property
checkCircuit c = conjoin [ property (testPoly p) | p <- elems (acSystem c) ]
    where
        testPoly p = do
            ins <- arbitrary
            let w = witnessGenerator c ins
                varF (NewVar v) = w ! v
                varF (InVar v)  = index ins v
            return $ evalPolynomial evalMonomial varF p === zero
