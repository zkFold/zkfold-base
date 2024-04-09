module ZkFold.Symbolic.GroebnerBasis
  ( module ZkFold.Symbolic.GroebnerBasis.Types,
    boundVariables,
    makeTheorem,
    verify,
    groebner,
    variableTypes,
    -- Internal
    lt,
    zeroM,
    zeroP,
    similarM,
    makeSPoly,
    fullReduceMany,
    groebnerStep,
    groebnerStepMax,
  )
where

import Data.Bool (bool)
import Data.List (nub, sortBy)
import Data.Map (Map, elems, empty, fromList, keys, mapWithKey, singleton, toList)
import Data.Maybe (mapMaybe)
import Numeric.Natural (Natural)
import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Field (Zp)
import ZkFold.Base.Algebra.Basic.Number (Prime)
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate as Poly
import ZkFold.Prelude ((!!))
import ZkFold.Symbolic.Compiler
import ZkFold.Symbolic.GroebnerBasis.Internal
import ZkFold.Symbolic.GroebnerBasis.Internal.Reduction
import ZkFold.Symbolic.GroebnerBasis.Internal.Types
import ZkFold.Symbolic.GroebnerBasis.Types
import Prelude hiding (Num (..), length, replicate, (!!))

boundVariables :: forall p. (Prime p) => Polynomial p -> [Polynomial p] -> Polynomial p
boundVariables p ps = foldr (makeBound . findVar) p $ zip [0 ..] ps
  where
    findVar :: (Natural, Polynomial p) -> (Natural, Variable p)
    findVar (k, h) = (i, v)
      where
        M _ as = lt h
        i = minimum $ keys as
        s = if k > 0 then makeSPoly (ps !! (k - 1)) h else zero
        s' = P [M one (singleton i (variable 2))] - P [M one (singleton i (variable 1))]
        v = bool (Bound 1 k) (Boolean k) $ zeroP $ s `reduce` s'

    makeBound :: (Natural, Variable p) -> Polynomial p -> Polynomial p
    makeBound (i, v) = makeBoundPolynomial
      where
        makeBoundVar :: Variable p -> Variable p
        makeBoundVar v' = setPower (getPower v') v

        makeBoundMonomial :: Monomial p -> Monomial p
        makeBoundMonomial (M c as) = M c $ mapWithKey (\j v' -> if j == i then makeBoundVar v' else v') as

        makeBoundPolynomial :: Polynomial p -> Polynomial p
        makeBoundPolynomial (P ms) = P $ map makeBoundMonomial ms

variableTypes :: forall p. (Prime p) => [Polynomial p] -> [(Monomial p, VarType)]
variableTypes = nub . sortBy (\(x1, _) (x2, _) -> compare x2 x1) . concatMap variableTypes'
  where
    variableTypes' :: Polynomial p -> [(Monomial p, VarType)]
    variableTypes' (P ms) = concatMap variableTypes'' ms

    variableTypes'' :: Monomial p -> [(Monomial p, VarType)]
    variableTypes'' (M _ as) = map (\(j, v) -> (M one (singleton j (setPower 1 v)), getVarType v)) $ toList as

makeTheorem :: forall p. (Prime p) => ArithmeticCircuit (Zp p) -> (Polynomial p, [Polynomial p])
makeTheorem r =
  ( boundVariables p0 ps, -- systemReduce $
    map (`boundVariables` ps) ps
  )
  where
    m = acSystem r
    xs = reverse $ elems $ acVarOrder r
    ps = sortBy (flip compare) $ map convert $ elems m

    k = acOutput r
    p0 = polynomial [M one (singleton (mapVars k) (Free 1))] - polynomial [M one empty]

    mapVars :: Natural -> Natural
    mapVars x
      | x == 0 = 0
      | otherwise = case lookup x (zip xs [1 ..]) of
          Just i -> i
          Nothing -> error $ "mapVars: variable " ++ show x ++ " not found!"

    convert :: Constraint (Zp p) -> Polynomial p
    convert (Poly.P ms) = polynomial $ map convert' ms
      where
        convert' :: (Zp p, Poly.M Natural Natural (Map Natural Natural)) -> Monomial p
        convert' (c, Poly.M as) = M c $ fromList $ mapMaybe convert'' $ toList as
          where
            convert'' :: (Natural, Natural) -> Maybe (Natural, Variable p)
            convert'' (j, i) =
              let ind = mapVars j
               in if ind > 0 then Just (ind, Free i) else Nothing

groebnerStepMax :: Integer
groebnerStepMax = 200

verify :: forall p. (Prime p) => (Polynomial p, [Polynomial p]) -> Bool
verify (p0, ps) = zeroP $ fst $ foldl (\args _ -> uncurry groebnerStep args) (p0, ps) [1 .. groebnerStepMax]

groebner :: forall p. (Prime p) => [Polynomial p] -> [Polynomial p]
groebner ps = snd $ foldl (\args _ -> uncurry groebnerStep args) (p, ps) [1 .. groebnerStepMax]
  where
    p = polynomial [lt $ head ps, monomial (negate one) empty]
