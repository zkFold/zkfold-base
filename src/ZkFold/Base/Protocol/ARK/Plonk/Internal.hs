{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.ARK.Plonk.Internal where

import           Control.Monad                                         (guard)
import           Data.Bifunctor                                        (first)
import           Data.Bool                                             (bool)
import           Data.Containers.ListUtils                             (nubOrd)
import           Data.List                                             (permutations, find, transpose, sort)
import           Data.Map                                              (Map, fromList, empty, elems, toList, delete)
import           Data.Maybe                                            (mapMaybe)
import           Prelude                                               hiding (Num(..), (^), (/), (!!), sum, length, take, drop)
import           System.Random                                         (RandomGen, Random (..), mkStdGen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                       (toZp, fromZp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381           (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate            (PolyVec, toPolyVec)
import           ZkFold.Base.Algebra.Polynomials.Multivariate          (SomePolynomial, P (..), M (..), polynomial, variables)
import           ZkFold.Prelude                                        (take, length)
import           ZkFold.Symbolic.Compiler

type F = ScalarField BLS12_381_G1
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

type SomePolynomialF = SomePolynomial F

-- TODO (Issue #15): safer code and better tests for this module

getParams :: Integer -> (F, F, F)
getParams l = findK' $ mkStdGen 0
    where
        omega = rootOfUnity l
        hGroup = map (omega^) [1 :: Integer .. 2^l-1]
        hGroup' k = map (k*) hGroup

        findK' :: RandomGen g => g -> (F, F, F)
        findK' g =
            let (k1, g') = first toZp $ randomR (1, order @F - 1) g
                (k2, g'') = first toZp $ randomR (1, order @F - 1) g'
            in bool (findK' g'') (omega, k1, k2) $
                all (`notElem` hGroup) (hGroup' k1)
                && all (`notElem` hGroup' k1) (hGroup' k2)

toPlonkConstaint :: SomePolynomialF -> (F, F, F, F, F, F, F, F)
toPlonkConstaint p@(P ms) =
    let xs    = nubOrd $ variables p
        i     = order @F
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0         -> [i, i, i]
            1         -> [i, i, head xs, head xs]
            2         -> [i] ++ xs ++ xs
            _         -> xs ++ xs

        getCoef :: Map Integer Integer -> F
        getCoef m = case find (\(_, M as) -> m == as) ms of
            Just (c, _) -> c
            _            -> zero

        getCoefs :: [Integer] -> Maybe (F, F, F, F, F, F, F, F)
        getCoefs [a, b, c] = do
            let xa = fromList [(a, 1)]
                xb = fromList [(b, 1)]
                xc = fromList [(c, 1)]
                xaxb = fromList [(a, 1), (b, 1)]

                ql = getCoef xa
                qr = getCoef xb
                qo = getCoef xc
                qm = getCoef xaxb
                qc = getCoef empty
            guard $ p - polynomial [(ql, M xa), (qr, M xb), (qo, M xc), (qm, M xaxb), (qc, M empty)] == zero
            return (ql, qr, qo, qm, qc, toZp a, toZp b, toZp c)
        getCoefs _ = Nothing

    in head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (F, F, F, F, F, F, F, F) -> SomePolynomialF
fromPlonkConstraint (ql, qr, qo, qm, qc, a, b, c) =
    let xa = fromList [(fromZp a, 1)]
        xb = fromList [(fromZp b, 1)]
        xc = fromList [(fromZp c, 1)]
        xaxb = fromList [(fromZp a, 1), (fromZp b, 1)]

    in polynomial [(ql, M xa), (qr, M xb), (qo, M xc), (qm, M xaxb), (qc, M empty)]

addPublicInput :: Integer -> F -> [SomePolynomialF] -> [SomePolynomialF]
addPublicInput i _ ps =
    polynomial [(one, M (fromList [(i, 1)]))] : ps

addPublicInputs :: Map Integer F -> [SomePolynomialF] -> [SomePolynomialF]
addPublicInputs inputs ps = foldr (\(i, x) ps' -> addPublicInput i x ps') ps $ toList inputs

removeConstantVariable :: SomePolynomialF -> SomePolynomialF
removeConstantVariable (P ms) =
    polynomial . map (\(c, M as) -> (c, M (0 `delete` as))) $ ms

toPlonkArithmetization :: forall a . Finite a => Map Integer F -> ArithmeticCircuit F
    -> (PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a)
toPlonkArithmetization inputs ac =
    let f (x0, x1, x2, x3, x4, x5, x6, x7) = [x0, x1, x2, x3, x4, x5, x6, x7]
        vars    = nubOrd $ sort $ 0 : concatMap variables (elems $ acSystem ac)
        ac'     = mapVarArithmeticCircuit ac
        inputs' = mapVarWitness vars inputs
        system  = addPublicInputs inputs' $ elems $ acSystem ac'

    in case map toPolyVec $ transpose $ map (f . toPlonkConstaint . removeConstantVariable) system of
            [ql, qr, qo, qm, qc, a, b, c] -> (ql, qr, qo, qm, qc, a, b, c)
            _                             -> error "toPlonkArithmetization: something went wrong"