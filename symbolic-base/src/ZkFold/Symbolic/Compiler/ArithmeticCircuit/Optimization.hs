module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Optimization (
        optimize,
        toConstVar
    ) where

import           Data.Bool                                               (bool)
import           Data.Functor                                            ((<&>))
import           Data.Functor.Rep                                        (Representable (..))
import           Data.Map                                                hiding (drop, foldl, foldr, map, null, splitAt,
                                                                          take)
import qualified Data.Map.Internal                                       as M
import qualified Data.Map.Monoidal                                       as MM
import           Data.Maybe                                              (catMaybes)
import qualified Data.Set                                                as S
import           Numeric.Natural                                         (Natural)
import           Prelude                                                 hiding (Num (..), drop, length, product,
                                                                          splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial   (Mono (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial (Poly (..), polynomial)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance     ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness      (WitnessF (..))

--------------------------------- High-level functions --------------------------------

-- | Replaces linear polynoms of the form
-- @(fromConstant k) * (NewVar nV) + (fromConstant c)@
-- with a constant variable @fromConstant $ negate c // k@ in an arithmetic circuit
-- and replaces variable with a constant in witness
--
optimize ::
  ( Arithmetic a, Ord (Rep i), Functor o) =>
  ArithmeticCircuit a p i o  -> ArithmeticCircuit a p i o
optimize ac = case catMaybes [toConstVar p | (_, p) <- toList (acSystem ac)] of
    [] -> ac
    vs -> optimize $ foldr optimize1 ac vs

optimize1 :: forall a p i o. (Arithmetic a, Ord (Rep i), Functor o)
  => (SysVar i , a )-> ArithmeticCircuit a p i o -> ArithmeticCircuit a p i o
optimize1 (v, k) ac = case v of
  NewVar nv -> ac {
      acSystem = M.filter (/= zero) (M.map optPoly $ acSystem ac),
      acRange =  MM.filter (/= S.empty) $ optRanges $ acRange ac,
      acWitness = (>>= optWitVar) <$> M.delete nv (acWitness ac),
      acOutput = acOutput ac <&> \case
        SysVar nV@(NewVar _) -> if nV == v then ConstVar k else SysVar nV
        o -> o
      }
  _ -> ac
  where
    optMono :: (a, Mono (SysVar i) Natural) -> (a, Mono (SysVar i) Natural)
    optMono mono@(c, M m) =
      case M.lookup v m of
        Just y -> (c * (k ^ y), M $ delete v m)
        _      -> mono

    optPoly :: Poly a (SysVar i) Natural -> Poly a (SysVar i) Natural
    optPoly (P (p :: [(a, Mono (SysVar i) Natural)])) = polynomial $ map optMono p

    optRanges :: MM.MonoidalMap a (S.Set (SysVar i)) -> MM.MonoidalMap a (S.Set (SysVar i))
    optRanges = MM.mapWithKey (\r s -> bool s (newS r s) (S.member v s) )
      where
        newS r s = bool (error "range constraint less then value") (S.filter (/= v) s) (k <= r)

    optWitVar :: WitVar p i -> WitnessF a (WitVar p i)
    optWitVar = \case
      (WSysVar (NewVar nV)) ->
        if NewVar nV == v
          then WitnessF $ const $ fromConstant k
          else pure $ WSysVar (NewVar nV)
      w  -> pure w


toConstVar :: (Arithmetic a, Ord (Rep i)) => Constraint a i -> Maybe (SysVar i, a)
toConstVar = \case
  P [(c, M m1), (k, M m2)] ->
    if m1 == empty
      then case toList m2 of
        [(m2var, 1)] -> Just ( m2var, negate c // k)
        _            -> Nothing
      else if m2 == empty
        then case toList m1 of
          [(m1var, 1)] -> Just ( m1var, negate k // c)
          _            -> Nothing
        else Nothing
  _ -> Nothing

