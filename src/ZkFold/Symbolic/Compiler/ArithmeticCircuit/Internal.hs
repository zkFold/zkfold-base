{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (
        ArithmeticCircuit(..),
        Var (..),
        VarField,
        Arithmetic,
        Constraint,
        -- variable getters
        acInput,
        getAllVars,
        -- evaluation functions
        witnessGenerator,
        eval,
        eval1,
        exec,
        exec1,
        apply,
    ) where

import           Control.DeepSeq                              (NFData, force)
import           Control.Monad.State                          (MonadState (..), State, modify, runState)
import           Data.Aeson
import           Data.ByteString                              (ByteString)
import           Data.Foldable                                (fold, toList)
import           Data.Functor.Rep
import           Data.Map.Strict                              hiding (drop, foldl, foldr, map, null, splitAt, take,
                                                               toList)
import           Data.Maybe                                   (fromJust)
import           Data.Semialign                               (unzipDefault)
import qualified Data.Set                                     as S
import           GHC.Generics                                 (Generic, Par1 (..), U1 (..), (:*:) (..))
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
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Poly, evalMonomial, evalPolynomial, mapCoeffs, var)
import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.ByteString                  (fromByteString, toByteString)
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.MonadCircuit

-- | The type that represents a constraint in the arithmetic circuit.
type Constraint c i = Poly c (Var i) Natural

-- | Arithmetic circuit in the form of a system of polynomial constraints.
data ArithmeticCircuit a i o = ArithmeticCircuit
    {
        acSystem  :: Map ByteString (Constraint a i),
        -- ^ The system of polynomial constraints
        acRange   :: Map ByteString a,
        -- ^ The range constraints [0, a] for the selected variables
        acWitness :: Map ByteString (i a -> Map ByteString a -> a),
        -- ^ The witness generation functions
        acRNG     :: StdGen,
        -- ^ random generator for generating unique variables
        acOutput  :: o (Var i)
        -- ^ The output variables
    } deriving (Generic)
deriving instance (NFData a, NFData (o (Var i)), NFData (Rep i))
    => NFData (ArithmeticCircuit a i o)

-- | A finite field of a large order.
-- It is used in the compiler for generating new variable indices.
type VarField = Zp BLS12_381_Scalar

data Var i
  = InVar (Rep i)
  | NewVar ByteString
  deriving Generic
deriving anyclass instance FromJSON (Rep i) => FromJSON (Var i)
deriving anyclass instance FromJSON (Rep i) => FromJSONKey (Var i)
deriving anyclass instance ToJSON (Rep i) => ToJSONKey (Var i)
deriving anyclass instance ToJSON (Rep i) => ToJSON (Var i)
deriving stock instance Show (Rep i) => Show (Var i)
deriving stock instance Eq (Rep i) => Eq (Var i)
deriving stock instance Ord (Rep i) => Ord (Var i)
deriving instance NFData (Rep i) => NFData (Var i)

---------------------------------- Variables -----------------------------------

acInput :: Representable i => i (Var i)
acInput = tabulate InVar

getAllVars :: (Representable i, Foldable i) => ArithmeticCircuit a i o -> [Var i]
getAllVars ac = toList acInput ++ map NewVar (keys $ acWitness ac)

--------------------------- Symbolic compiler context --------------------------

crown :: ArithmeticCircuit a i g -> f (Var i) -> ArithmeticCircuit a i f
crown = flip (set #acOutput)

behead :: ArithmeticCircuit a i f -> (ArithmeticCircuit a i U1, f (Var i))
behead = liftA2 (,) (set #acOutput U1) acOutput

instance HFunctor (ArithmeticCircuit a i) where
    hmap = over #acOutput

instance HApplicative (ArithmeticCircuit a i) where
    hpure = crown mempty
    hliftA2 f (behead -> (c, o)) (behead -> (d, p)) = crown (c <> d) (f o p)

instance Package (ArithmeticCircuit a i) where
    unpackWith f (behead -> (c, o)) = crown c <$> f o
    packWith f (unzipDefault . fmap behead -> (cs, os)) = crown (fold cs) (f os)

instance
  ( Arithmetic a, Ord (Rep i), Representable i, Foldable i
  , ToConstant (Rep i), Const (Rep i) ~ Natural
  ) => Symbolic (ArithmeticCircuit a i) where
    type BaseField (ArithmeticCircuit a i) = a
    symbolicF (behead -> (c, o)) _ f = uncurry (set #acOutput) (runState (f o) c)

----------------------------- MonadCircuit instance ----------------------------

instance
  ( Arithmetic a, Ord (Rep i), Representable i, Foldable i, o ~ U1
  , ToConstant (Rep i), Const (Rep i) ~ Natural
  ) => MonadCircuit (Var i) a (State (ArithmeticCircuit a i o)) where

    newRanged upperBound witness = do
      i <- unconstrained witness
          (\x v -> let b = fromConstant upperBound
                    in b * x v * (x v - b))
          -- ^ A wild (and obviously incorrect) approximation of
          -- x (x - 1) ... (x - upperBound)
          -- It's ok because we only use it for variable generation anyway.
      zoom #acRange . modify $ insert i upperBound
      return (NewVar i)

    newConstrained new witness = do
      i <- unconstrained witness new
      constraint (`new` NewVar i)
      return (NewVar i)

    constraint p = do
      let c = p var
      zoom #acSystem . modify $ insert (toVar [] c) c

unconstrained ::
  forall a i.
  (Arithmetic a, Ord (Rep i), ToConstant (Rep i), Const (Rep i) ~ Natural) =>
  (Representable i, Foldable i) =>
  Witness (Var i) a -> NewConstraint (Var i) a ->
  State (ArithmeticCircuit a i U1) ByteString
unconstrained witness con = do
  raw <- toByteString @VarField . fromConstant . fst <$> do
    zoom #acRNG (get >>= traverse put . uniformR (0, order @VarField -! 1))
  let sources = runSources . ($ Sources @a . S.singleton)
      srcs = sources witness `S.difference` sources (`con` NewVar mempty)
      v = toVar @a @i (S.toList srcs) $ con var (NewVar raw)
  -- TODO: forbid reassignment of variables
  zoom #acWitness . modify $ insert v $ \i w -> witness $ \case
    InVar inV -> index i inV
    NewVar newV -> w ! newV
  return v

-- TODO: Remove the hardcoded constant.
toVar ::
  forall a i.
  (Arithmetic a, ToConstant (Rep i), Const (Rep i) ~ Natural) =>
  (Representable i, Foldable i) => [Var i] -> Constraint a i -> ByteString
toVar srcs c = force (toByteString ex)
    where
        l  = Haskell.fromIntegral (Haskell.length @i acInput)
        r  = toZp 903489679376934896793395274328947923579382759823 :: VarField
        g  = toZp 89175291725091202781479751781509570912743212325 :: VarField
        varF (NewVar w)  = toConstant (fromJust $ fromByteString @VarField w) + l
        varF (InVar inV) = toConstant inV
        v  = (+ r) . fromConstant . varF
        x  = g ^ fromZp (evalPolynomial evalMonomial v $ mapCoeffs toConstant c)
        ex = foldr (\p y -> x ^ varF p + y) x srcs

-------------------------------- Circuit monoid --------------------------------

instance o ~ U1 => Semigroup (ArithmeticCircuit a i o) where
    c1 <> c2 =
        ArithmeticCircuit
           {   acSystem   = acSystem c1 `union` acSystem c2
           ,   acRange    = acRange c1 `union` acRange c2
           ,   acWitness  = acWitness c1 `union` acWitness c2
           ,   acRNG      = mkStdGen $ fst (uniform (acRNG c1)) Haskell.* fst (uniform (acRNG c2))
           ,   acOutput   = U1
           }

instance o ~ U1 => Monoid (ArithmeticCircuit a i o) where
    mempty =
        ArithmeticCircuit
           {
               acSystem   = empty,
               acRange    = empty,
               acWitness  = empty,
               acRNG      = mkStdGen 0,
               acOutput   = U1
           }

----------------------------- Evaluation functions -----------------------------

witnessGenerator :: ArithmeticCircuit a i o -> i a -> Map ByteString a
witnessGenerator circuit inputs =
  let result = fmap (\k -> k inputs result) (acWitness circuit)
  in result

-- | Evaluates the arithmetic circuit with one output using the supplied input map.
eval1 :: Representable i => ArithmeticCircuit a i Par1 -> i a -> a
eval1 ctx i = unPar1 (eval ctx i)

-- | Evaluates the arithmetic circuit using the supplied input map.
eval :: (Representable i, Functor o) => ArithmeticCircuit a i o -> i a -> o a
eval ctx i = acOutput ctx <&> \case
    NewVar k -> witnessGenerator ctx i ! k
    InVar j -> index i j

-- | Evaluates the arithmetic circuit with no inputs and one output.
exec1 :: ArithmeticCircuit a U1 Par1 -> a
exec1 ac = eval1 ac U1

-- | Evaluates the arithmetic circuit with no inputs.
exec :: Functor o => ArithmeticCircuit a U1 o -> o a
exec ac = eval ac U1

-- | Applies the values of the first couple of inputs to the arithmetic circuit.
apply ::
  (Eq a, Field a, Ord (Rep j), Representable i) =>
  i a -> ArithmeticCircuit a (i :*: j) U1 -> ArithmeticCircuit a j U1
apply xs ac = ac
  { acSystem = fmap (evalPolynomial evalMonomial varF) (acSystem ac)
  , acWitness = fmap witF (acWitness ac)
  , acOutput = U1
  }
  where
    varF (InVar (Left v))  = fromConstant (index xs v)
    varF (InVar (Right v)) = var (InVar v)
    varF (NewVar v)        = var (NewVar v)
    witF f j = f (xs :*: j)

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
