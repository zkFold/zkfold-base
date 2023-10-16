module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (
    module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Types,
    boundVariables,
    fromR1CS,
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
    groebnerStepMax
    ) where

import           Data.Bool                         (bool)
import           Data.List                         (sortBy, nub)
import           Data.Map                          (Map, toList, elems, empty, singleton, keys, mapWithKey)
import           Prelude                           hiding (Num(..), (!!), length, replicate)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field (Zp)
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal.Reduction
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal.Types
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Types
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Prelude                    ((!!))

boundVariables :: forall p . Prime p => Polynomial p -> [Polynomial p] -> Polynomial p
boundVariables p ps = foldr (makeBound . findVar) p $ zip [0..] ps
    where
        findVar :: (Integer, Polynomial p) -> (Integer, Variable p)
        findVar (k, h) = (i, v)
            where
                M _ as = lt h
                i = minimum $ keys as
                s = if k > 0 then makeSPoly (ps !! (k-1)) h else zero
                s' = P [M one (singleton i (variable 2))] - P [M one (singleton i (variable 1))]
                v = bool (Bound 1 k) (Boolean k) $ zeroP $ s `reduce` s'

        makeBound :: (Integer, Variable p) -> Polynomial p -> Polynomial p
        makeBound (i, v) = makeBoundPolynomial
            where
                makeBoundVar :: Variable p -> Variable p
                makeBoundVar v' = setPower (getPower v') v

                makeBoundMonomial :: Monomial p -> Monomial p
                makeBoundMonomial (M c as) = M c $ mapWithKey (\j v' -> if j == i then makeBoundVar v' else v') as

                makeBoundPolynomial :: Polynomial p -> Polynomial p
                makeBoundPolynomial (P ms) = P $ map makeBoundMonomial ms

variableTypes :: forall p . Prime p => [Polynomial p] -> [(Monomial p, VarType)]
variableTypes = nub . sortBy (\(x1, _) (x2, _) -> compare x2 x1) . concatMap variableTypes'
    where
        variableTypes' :: Polynomial p -> [(Monomial p, VarType)]
        variableTypes' (P ms) = concatMap variableTypes'' ms

        variableTypes'' :: Monomial p -> [(Monomial p, VarType)]
        variableTypes'' (M _ as) = map (\(j, v) -> (M one (singleton j (setPower 1 v)), getVarType v)) $ toList as

fromR1CS :: forall p t s . Prime p => R1CS (Zp p) t s -> (Polynomial p, [Polynomial p])
fromR1CS r = (boundVariables p0 ps, --systemReduce $
        map (`boundVariables` ps) ps)
    where
        m  = r1csSystem r
        xs = reverse $ elems $ r1csVarOrder r
        ps = sortBy (flip compare) $ map fromR1CS' $ elems m

        k  = head $ r1csOutput r
        p0 = polynomial [var k one] - polynomial [var 0 one]

        mapVars :: Integer -> Integer
        mapVars x
            | x == 0    = 0
            | otherwise = case lookup x (zip xs [1..]) of
                Just i  -> i
                Nothing -> error $ "mapVars: variable " ++ show x ++ " not found!"

        var :: Integer -> Zp p -> Monomial p
        var i v =
            let j = mapVars i
            in M v $ if j > 0 then singleton j (Free 1) else empty

        fromR1CS' :: (Map Integer (Zp p), Map Integer (Zp p), Map Integer (Zp p)) -> Polynomial p
        fromR1CS' (a, b, c) = mulM pa pb `addPoly` mulPM pc (M (negate 1) empty)
            where
                pa = polynomial $ map (uncurry var) $ toList a
                pb = polynomial $ map (uncurry var) $ toList b
                pc = polynomial $ map (uncurry var) $ toList c

groebnerStepMax :: Integer
groebnerStepMax = 200

verify :: forall p . Prime p => (Polynomial p, [Polynomial p]) -> Bool
verify (p0, ps) = zeroP $ fst $ foldl (\args _ -> uncurry groebnerStep args) (p0, ps) [1..groebnerStepMax]

groebner :: forall p . Prime p => [Polynomial p] -> [Polynomial p]
groebner ps = snd $ foldl (\args _ -> uncurry groebnerStep args) (p, ps) [1..groebnerStepMax]
    where p = polynomial [lt $ head ps, monomial (negate one) empty]