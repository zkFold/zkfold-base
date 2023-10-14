module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (
    module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Types,
    boundVariables,
    fromR1CS,
    verify,
    -- Internal
    lt,
    zeroM,
    zeroP,
    similarM,
    makeSPoly,
    fullReduceMany,
    groebnerStep
    ) where

import           Data.List                         (sortBy)
import           Data.Map                          (Map, toList, elems, empty, singleton, keys, mapWithKey)
import           Prelude                           hiding (Num(..), (!!), length, replicate)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field (Zp)
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal.Reduction
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal.Types
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Types
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS

boundVariables :: [Polynomial p] -> Polynomial p -> Polynomial p
boundVariables qs p = foldr (\(s, i) q -> makeBound i s q) p $ zip [0..] $ map findVar qs
    where
        findVar :: Polynomial p -> Integer
        findVar h = minimum $ keys as
            where M _ as = lt h

        makeBound :: Integer -> Integer -> Polynomial p -> Polynomial p
        makeBound i s = makeBoundPolynomial
            where
                makeBoundVar :: Variable p -> Variable p
                makeBoundVar v = Bound (getPower v) s

                makeBoundMonomial :: Monomial p -> Monomial p
                makeBoundMonomial (M c as) = M c $ mapWithKey (\j v -> if j == i then makeBoundVar v else v) as

                makeBoundPolynomial :: Polynomial p -> Polynomial p
                makeBoundPolynomial (P ms) = P $ map makeBoundMonomial ms

fromR1CS :: forall p t s . Prime p => R1CS (Zp p) t s -> (Polynomial p, [Polynomial p])
fromR1CS r = (boundVariables ps p0, ps')
    where
        m  = r1csSystem r
        xs = reverse $ elems $ r1csVarOrder r
        ps = systemReduce $
            sortBy (flip compare) $ map fromR1CS' $ elems m

        ps' = map (boundVariables ps) ps
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

verify :: forall p . Prime p => (Polynomial p, [Polynomial p]) -> Bool
verify (p0, ps) = zeroP $ fst $ foldl (\args _ -> uncurry groebnerStep args) (p0, ps) [1::Integer ..200]