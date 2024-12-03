module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Optimization (
        optimize,
        toConstVar
    ) where

import           Data.Binary                                             (Binary)
import           Data.Bool                                               (bool)
import           Data.ByteString                                         (ByteString)
import           Data.Functor                                            ((<&>))
import           Data.Functor.Rep                                        (Representable (..))
import           Data.Map                                                hiding (drop, foldl, foldr, map, null, splitAt,
                                                                          take)
import qualified Data.Map.Internal                                       as M
import qualified Data.Map.Monoidal                                       as MM
import qualified Data.Set                                                as S
import           Prelude                                                 hiding (Num (..), drop, length, product,
                                                                          splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate            (evalMonomial)
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial   (Mono (..), oneM)
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial (Poly (..), evalPolynomial, var)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance     ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MerkleHash   (merkleHash, runHash)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness      (WitnessF (..))

--------------------------------- High-level functions --------------------------------

-- | Replaces linear polynoms of the form
-- @(fromConstant k) * (NewVar nV) + (fromConstant c)@
-- with a constant variable @fromConstant $ negate c // k@ in an arithmetic circuit
-- and replaces variable with a constant in witness
--
optimize ::
   (Arithmetic a, Ord (Rep i), Functor o, Binary (Rep i)) =>
  ArithmeticCircuit a p i o  -> ArithmeticCircuit a p i o
optimize ac = let (newAcSystem, vs) = varsToReplace (acSystem ac, M.empty) in optimizeAc vs ac {acSystem = newAcSystem}

varsToReplace ::
  (Arithmetic a, Ord (Rep i)) =>
  (Map ByteString (Constraint a i) , Map (SysVar i) a) -> (Map ByteString (Constraint a i) , Map (SysVar i) a)
varsToReplace (s, l) = let newVars = M.fromList . M.elems $ mapMaybe toConstVar s in
  if newVars == M.empty
  then (s, l)
  else varsToReplace (optimizeSystems newVars s, M.union newVars l)

optimizeSystems :: (Arithmetic a, Ord (Rep i)) =>
  Map (SysVar i) a -> Map ByteString (Constraint a i) -> Map ByteString (Constraint a i)
optimizeSystems m as = M.filter (/= zero) $ evalPolynomial evalMonomial varF <$> as
  where
    varF p = maybe (var p) fromConstant (M.lookup p m)

optimizeAc :: forall a p i o. (Arithmetic a, Ord (Rep i), Functor o, Binary (Rep i))
  => Map (SysVar i) a-> ArithmeticCircuit a p i o -> ArithmeticCircuit a p i o
optimizeAc vs ac =
    ac {
      acSystem = addInVarConstraints $ acSystem ac,
      acRange =  MM.filter (/= S.empty) $ optRanges vs (acRange ac),
      acWitness = (>>= optWitVar vs) <$> M.filterWithKey (\k _ -> notMember (NewVar k) vs) (acWitness ac),
      acOutput = acOutput ac <&> \case
        SysVar sV -> maybe (SysVar sV) ConstVar (M.lookup sV vs)
        o -> o
      }
  where
    addInVarConstraints :: Map ByteString (Poly a (SysVar i) Natural) -> Map ByteString (Poly a (SysVar i) Natural)
    addInVarConstraints p = foldrWithKey (\k a as -> case k of
      inVar@(InVar inV) -> M.insert (runHash @(Just (Order a)) $ merkleHash inV) (var inVar - fromConstant a) as
      _                 -> as) p vs

    optRanges :: Map (SysVar i) a -> MM.MonoidalMap a (S.Set (SysVar i)) -> MM.MonoidalMap a (S.Set (SysVar i))
    optRanges m = MM.mapWithKey (\r s -> bool (error "range constraint less then value") (S.difference s $ keysSet m) (all (<= r) $ restrictKeys m s))

    optWitVar :: Map (SysVar i) a -> WitVar p i -> WitnessF a (WitVar p i)
    optWitVar m = \case
      (WSysVar sv) ->
        case M.lookup sv m of
          Just k  -> WitnessF $ const $ fromConstant k
          Nothing -> pure $ WSysVar sv
      w  -> pure w

toConstVar :: (Arithmetic a) => Constraint a i -> Maybe (SysVar i, a)
toConstVar = \case
  P [(_, M m1)] -> case toList m1 of
    [(m1var, 1)] -> Just (m1var, zero)
    _            -> Nothing
  P [(c, M m1), (k, M m2)] ->
    if oneM (M m1)
      then case toList m2 of
        [(m2var, 1)] -> Just (m2var, negate c // k)
        _            -> Nothing
      else if oneM (M m2)
        then case toList m1 of
          [(m1var, 1)] -> Just (m1var, negate k // c)
          _            -> Nothing
        else Nothing
  _ -> Nothing
