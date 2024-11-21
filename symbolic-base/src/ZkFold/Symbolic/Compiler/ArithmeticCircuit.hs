{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        Constraint,
        Var,
        witnessGenerator,
        -- high-level functions
        optimize,
        desugarRanges,
        idCircuit,
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
        mapVarArithmeticCircuit,
        -- Arithmetization type fields
        acWitness,
        acInput,
        acOutput,
        -- Testing functions
        checkCircuit,
        checkClosedCircuit
    ) where

import           Control.DeepSeq                                         (NFData)
import           Control.Monad                                           (foldM)
import           Control.Monad.State                                     (State, execState, modify)
import           Data.Binary                                             (Binary)
import           Data.Foldable                                           (for_)
import           Data.Functor.Rep                                        (Representable (..), mzipRep)
import           Data.Map                                                hiding (drop, foldl, foldr, map, null, splitAt,
                                                                          take)
import qualified Data.Map.Internal                                       as M
import qualified Data.Map.Monoidal                                       as MM
import qualified Data.Set                                                as S
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
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial   (Mono (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial (Poly (..))
import           ZkFold.Base.Data.HFunctor                               (hmap)
import           ZkFold.Base.Data.Product                                (fstP, sndP)
import           ZkFold.Prelude                                          (length)
import           ZkFold.Symbolic.Class                                   (fromCircuit2F)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance     ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal     (Arithmetic, ArithmeticCircuit (..),
                                                                          Constraint, SysVar (..), Var (..),
                                                                          WitVar (..), acInput, eval, eval1, exec,
                                                                          exec1, hlmap, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness      (WitnessF (..))
import           ZkFold.Symbolic.Data.Combinators                        (expansion)
import           ZkFold.Symbolic.MonadCircuit                            (MonadCircuit (..))

--------------------------------- High-level functions --------------------------------

-- | Optimizes the constraint system.
--
optimize1 :: forall a p i o. ( Arithmetic a, Ord (Rep i))
  => SysVar i -> a -> State (ArithmeticCircuit a p i o) ()
optimize1 v k = case v of
  NewVar nv -> modify (\(f :: ArithmeticCircuit a p i o) ->
    f {
      acSystem = M.map optPoly $ acSystem f,
      acRange = optRanges $ acRange f,
      acWitness = M.map optWitVar $ M.delete nv $ acWitness f
      })
  _ -> error "This shouldn't happen"
  where
    optMono :: (a, Mono (SysVar i) Natural) -> (a, Mono (SysVar i) Natural)
    optMono mono@(c, M m) =
      case M.lookup v m of
        Just y -> (c * k ^ y, M $ delete v m)
        _      -> mono

    optPoly :: Poly a (SysVar i) Natural -> Poly a (SysVar i) Natural
    optPoly (P (p :: [(a, Mono (SysVar i) Natural)])) = P $
      map optMono p

    optRanges :: MM.MonoidalMap a (S.Set (SysVar i)) -> MM.MonoidalMap a (S.Set (SysVar i))
    optRanges = MM.mapWithKey (\i s ->
      if S.member v s && k <= i
        then S.filter (/= v) s
        else s)

    optWitVar ::  WitnessF a (WitVar p i) -> WitnessF a (WitVar p i)
    optWitVar (WitnessF w)  = WitnessF $ \ww -> w $ \case
      WSysVar nV@(NewVar _) ->
        if v == nV
        then ww (WSysVar nV)
        else fromConstant k
      x -> ww x

optimize ::
  ( Arithmetic a, Ord (Rep i)) =>
  ArithmeticCircuit a p i o  -> ArithmeticCircuit a p i o
optimize = until (not . haveOptimal) f
  where
    f ac = flip execState ac . traverse (uncurry optimize1) $ [toConstVar p | (_, p) <- toList (acSystem ac), isLinear p  ]

haveOptimal ::( Ord (Rep i)) => ArithmeticCircuit a p i o  -> Bool
haveOptimal c = any (isLinear . snd) (toList (acSystem c))

toConstVar :: (Arithmetic a, Ord (Rep i)) => Constraint a i -> (SysVar i, a)
toConstVar = \case
  P [(c, M m1), (k, M m2)] -> if m1 == empty
    then case toList m2 of
      [(m2var, 1)] -> ( m2var, negate c // k)
      _            -> error "this shouldn't happen because isLinear"
    else case toList m1 of
      [(m1var, 1)] -> ( m1var, negate k // c)
      _            -> error "this shouldn't happen because isLinear"
  _ -> error "this shouldn't happen because isLinear"

isLinear :: (Ord (Rep i)) => Constraint a i -> Bool
isLinear = \case
  P [(_, M m1) , (_, M m2)] ->
    m1 == empty && (case toList m2 of
      [( NewVar _ , 1)] -> True
      _                 -> False) ||
    m2 == empty && (case toList m1 of
      [( NewVar _ , 1)] -> True
      _                 -> False)
  _ -> False


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
  let r' = flip execState c {acOutput = U1} . traverse (uncurry desugarRange) $ [(SysVar v, k) | (k, s) <- MM.toList (acRange c), v <- S.toList s]
   in r' { acRange = mempty, acOutput = acOutput c }

idCircuit :: Representable i => ArithmeticCircuit a p i i
idCircuit = ArithmeticCircuit
  { acSystem = empty
  , acRange = MM.empty
  , acWitness = empty
  , acOutput = acInput
  }

guessOutput ::
  (Arithmetic a, Binary a, Binary (Rep p), Binary (Rep i), Binary (Rep o)) =>
  (Ord (Rep i), Ord (Rep o), NFData (Rep i), NFData (Rep o)) =>
  (Representable i, Representable o, Foldable o) =>
  ArithmeticCircuit a p i o -> ArithmeticCircuit a p (i :*: o) U1
guessOutput c = fromCircuit2F (hlmap fstP c) (hmap sndP idCircuit) $ \o o' -> do
  for_ (mzipRep o o') $ \(i, j) -> constraint (\x -> x i - x j)
  return U1

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a p i o -> Natural
acSizeN = length . acSystem

-- | Calculates the number of variables in the system.
acSizeM :: ArithmeticCircuit a p i o -> Natural
acSizeM = length . acWitness

-- | Calculates the number of range lookups in the system.
acSizeR :: ArithmeticCircuit a p i o -> Natural
acSizeR = sum . map length . MM.elems . acRange

acValue :: (Arithmetic a, Functor o) => ArithmeticCircuit a U1 U1 o -> o a
acValue = exec

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint ::
  (Arithmetic a, Show a, Show (o (Var a U1)), Show (o a), Functor o) =>
  ArithmeticCircuit a U1 U1 o -> IO ()
acPrint ac = do
    let m = elems (acSystem ac)
        w = witnessGenerator ac U1 U1
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
    :: forall a o
     . Arithmetic a
    => Show a
    => ArithmeticCircuit a U1 U1 o
    -> Property
checkClosedCircuit c = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem c) ]
    where
        w = witnessGenerator c U1 U1
        testPoly p = evalPolynomial evalMonomial varF p === zero
        varF (NewVar v) = w ! v
        varF (InVar v)  = absurd v

checkCircuit
    :: Arbitrary (p a)
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
            let w = witnessGenerator c pls ins
                varF (NewVar v) = w ! v
                varF (InVar v)  = index ins v
            return $ evalPolynomial evalMonomial varF p === zero
