{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Arithmetic,
        ConstraintMonomial,
        Constraint,
        witnessGenerator,
        -- low-level functions
        constraint,
        rangeConstraint,
        assignment,
        addVariable,
        newVariableWithSource,
        eval,
        eval1,
        exec,
        exec1,
        apply,
    ) where

import           Control.DeepSeq                              (NFData, force)
import           Control.Monad.State                          (MonadState (..), State, gets, modify, runState)
import           Data.Foldable                                (fold)
import           Data.Map.Strict                              hiding (drop, foldl, foldr, map, null, splitAt, take)
import qualified Data.Map.Strict                              as M
import           Data.Semialign                               (unzipDefault)
import qualified Data.Set                                     as S
import           GHC.Generics                                 (Generic, Par1 (..), U1 (..))
import           Optics
import           Prelude                                      hiding (Num (..), drop, length, product, splitAt, sum,
                                                               take, (!!), (^))
import qualified Prelude                                      as Haskell
import           System.Random                                (StdGen, mkStdGen, uniform, uniformR)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.Sources
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_Scalar)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Mono, Poly, evalMonomial, evalPolynomial, mapCoeffs, var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Prelude                               (drop, length)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.MonadCircuit

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a o = ArithmeticCircuit
    {
        acSystem   :: Map Natural (Constraint a),
        -- ^ The system of polynomial constraints
        acRange    :: Map Natural a,
        -- ^ The range constraints [0, a] for the selected variables
        acInput    :: [Natural],
        -- ^ The input variables
        acWitness  :: Map Natural (Map Natural a -> a),
        -- ^ The witness generation functions
        acVarOrder :: Map (Natural, Natural) Natural,
        -- ^ The order of variable assignments
        acRNG      :: StdGen,
        -- ^ random generator for generating unique variables
        acOutput   :: o Natural
        -- ^ The output variables
    } deriving (Generic)
deriving instance (NFData a, NFData (o Natural))
    => NFData (ArithmeticCircuit a o)

witnessGenerator :: ArithmeticCircuit a o -> Map Natural a -> Map Natural a
witnessGenerator circuit inputs =
  let srcs = acWitness circuit
      witness = ($ witness) <$> (srcs `union` fmap const inputs)
   in witness

------------------------------ Symbolic compiler context ----------------------------

crown :: ArithmeticCircuit a g -> f Natural -> ArithmeticCircuit a f
crown = flip (set #acOutput)

behead :: ArithmeticCircuit a f -> (ArithmeticCircuit a U1, f Natural)
behead = liftA2 (,) (set #acOutput U1) acOutput

instance HFunctor (ArithmeticCircuit a) where
    hmap = over #acOutput

instance (Eq a, MultiplicativeMonoid a) => HApplicative (ArithmeticCircuit a) where
    hpure = crown mempty
    hliftA2 f (behead -> (c, o)) (behead -> (d, p)) = crown (c <> d) (f o p)

instance (Eq a, MultiplicativeMonoid a) => Package (ArithmeticCircuit a) where
    unpackWith f (behead -> (c, o)) = crown c <$> f o
    packWith f (unzipDefault . fmap behead -> (cs, os)) = crown (fold cs) (f os)

instance Arithmetic a => Symbolic (ArithmeticCircuit a) where
    type BaseField (ArithmeticCircuit a) = a
    symbolicF (behead -> (c, o)) _ f = uncurry (set #acOutput) (runState (f o) c)

-------------------------------- MonadCircuit instance ------------------------------

instance (Arithmetic a, o ~ U1) => MonadCircuit Natural a (State (ArithmeticCircuit a o)) where
    newRanged upperBound witness = do
        let s   = sources @a witness
            b   = fromConstant upperBound
            -- | A wild (and obviously incorrect) approximation of
            -- x (x - 1) ... (x - upperBound)
            -- It's ok because we only use it for variable generation anyway.
            p i = b * var i * (var i - b)
        i <- addVariable =<< newVariableWithSource (S.toList s) p
        rangeConstraint i upperBound
        assignment i (\m -> witness (m !))
        return i

    newConstrained
        :: NewConstraint Natural a
        -> Witness Natural a
        -> State (ArithmeticCircuit a U1) Natural
    newConstrained new witness = do
        let ws = sources @a witness
            -- | We need a throwaway variable to feed into `new` which definitely would not be present in a witness
            x = maximum (S.mapMonotonic (+1) ws <> S.singleton 0)
            -- | `s` is meant to be a set of variables used in a witness not present in a constraint.
            s = ws `S.difference` sources @a (`new` x)
        i <- addVariable =<< newVariableWithSource (S.toList s) (new var)
        constraint (`new` i)
        assignment i (\m -> witness (m !))
        return i

    constraint p = addConstraint (p var)

sources :: forall a i . (FiniteField a, Ord i) => Witness i a -> S.Set i
sources = runSources . ($ Sources @a . S.singleton)

----------------------------------- Circuit monoid ----------------------------------

instance (Eq a, o ~ U1) => Semigroup (ArithmeticCircuit a o) where
    c1 <> c2 =
        ArithmeticCircuit
           {
               acSystem   = acSystem c1 `union` acSystem c2
            ,  acRange    = acRange c1 `union` acRange c2
               -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
               -- We need a way to ensure the correct order no matter how `(<>)` is used.
           ,   acInput    = nubConcat (acInput c1) (acInput c2)
           ,   acWitness  = acWitness c1 `union` acWitness c2
           ,   acVarOrder = acVarOrder c1 `union` acVarOrder c2
           ,   acRNG      = mkStdGen $ fst (uniform (acRNG c1)) Haskell.* fst (uniform (acRNG c2))
           ,   acOutput   = U1
           }

nubConcat :: Ord a => [a] -> [a] -> [a]
nubConcat l r = l ++ Prelude.filter (`S.notMember` lSet) r
    where
        lSet = S.fromList l

instance (Eq a, MultiplicativeMonoid a, o ~ U1) => Monoid (ArithmeticCircuit a o) where
    mempty =
        ArithmeticCircuit
           {
               acSystem   = empty,
               acRange    = empty,
               acInput    = [],
               acWitness  = singleton 0 one,
               acVarOrder = empty,
               acRNG      = mkStdGen 0,
               acOutput   = U1
           }

------------------------------------- Variables -------------------------------------

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = Zp BLS12_381_Scalar

toField :: Arithmetic a => a -> VarField
toField = toZp . fromConstant . fromBinary @Natural . castBits . binaryExpansion

-- TODO: Remove the hardcoded constant.
toVar :: Arithmetic a => [Natural] -> Constraint a -> Natural
toVar srcs c = force $ fromZp ex
    where
        r  = toZp 903489679376934896793395274328947923579382759823 :: VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: VarField
        v  = (+ r) . fromConstant
        x  = g ^ fromZp (evalPolynomial evalMonomial v $ mapCoeffs toField c)
        ex = foldr (\p y -> x ^ p + y) x srcs

newVariableWithSource :: Arithmetic a => [Natural] -> (Natural -> Constraint a) -> State (ArithmeticCircuit a U1) Natural
newVariableWithSource srcs con = toVar srcs . con . fst <$> do
    zoom #acRNG $ get >>= traverse put . uniformR (0, order @VarField -! 1)

addVariable :: Natural -> State (ArithmeticCircuit a U1) Natural
addVariable x = do
    zoom #acVarOrder . modify
        $ \vo -> insert (Haskell.fromIntegral $ M.size vo, x) x vo
    pure x

---------------------------------- Low-level functions --------------------------------

type ConstraintMonomial = Mono Natural Natural

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c = Poly c Natural Natural

-- | Adds a constraint to the arithmetic circuit.
addConstraint :: Arithmetic a => Constraint a -> State (ArithmeticCircuit a U1) ()
addConstraint c = zoom #acSystem . modify $ insert (toVar [] c) c

rangeConstraint :: Natural -> a -> State (ArithmeticCircuit a U1) ()
rangeConstraint i b = zoom #acRange . modify $ insert i b

-- | Adds a new variable assignment to the arithmetic circuit.
-- TODO: forbid reassignment of variables
assignment :: Natural -> (Map Natural a -> a) -> State (ArithmeticCircuit a U1) ()
assignment i f = zoom #acWitness . modify $ insert i f

-- | Evaluates the arithmetic circuit with one output using the supplied input map.
eval1 :: ArithmeticCircuit a Par1 -> Map Natural a -> a
eval1 ctx i = witnessGenerator ctx i ! unPar1 (acOutput ctx)

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: Functor o => ArithmeticCircuit a o -> Map Natural a -> o a
eval ctx i = (witnessGenerator ctx i !) <$> acOutput ctx

-- | Evaluates the arithmetic circuit with no inputs and one output using the supplied input map.
exec1 :: ArithmeticCircuit a Par1 -> a
exec1 ac = eval1 ac empty

-- | Evaluates the arithmetic circuit with no inputs using the supplied input map.
exec :: Functor o => ArithmeticCircuit a o -> o a
exec ac = eval ac empty

-- | Applies the values of the first `n` inputs to the arithmetic circuit.
-- TODO: make this safe
apply :: [a] -> State (ArithmeticCircuit a U1) ()
apply xs = do
    inputs <- gets acInput
    zoom #acInput . put $ drop (length xs) inputs
    zoom #acWitness . modify . union . fromList $ zip inputs (map const xs)

-- TODO: Add proper symbolic application functions

-- applySymOne :: ArithmeticCircuit a -> State (ArithmeticCircuit a) ()
-- applySymOne x = modify (\(f :: ArithmeticCircuit a) ->
--     let ins = acInput f
--     in f
--     {
--         acInput = tail ins,
--         acWitness = acWitness f . (singleton (head ins) (eval x empty)  `union`)
--     })

-- applySym :: [ArithmeticCircuit a] -> State (ArithmeticCircuit a) ()
-- applySym = foldr ((>>) . applySymOne) (return ())

-- applySymArgs :: ArithmeticCircuit a -> [ArithmeticCircuit a] -> ArithmeticCircuit a
-- applySymArgs x xs = execState (applySym xs) x
