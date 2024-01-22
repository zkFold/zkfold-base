{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.ARK.Plonk.Internal where

import           Control.Monad                                         (guard)
import           Data.Bifunctor                                        (first)
import           Data.Bool                                             (bool)
import           Data.Containers.ListUtils                             (nubOrd)
import           Data.List                                             (permutations, find, transpose, sort)
import           Data.Map                                              (Map, keys, fromList, empty, elems, toList, delete)
import           Data.Maybe                                            (mapMaybe)
import           Prelude                                               hiding (Num(..), (^), (/), (!!), sum, length, take, drop)
import           System.Random                                         (RandomGen, Random (..), mkStdGen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                       (toZp, fromZp)
import           ZkFold.Base.Algebra.Polynomials.Univariate            (PolyVec, toPolyVec)
import           ZkFold.Base.Algebra.Polynomials.Multivariate          (Polynomial, getMonomials, getPowers, polynomial)
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Internal (Monom(..), Var(..))
import           ZkFold.Base.Protocol.Commitment.KZG
import           ZkFold.Prelude                                        (take, length)
import           ZkFold.Symbolic.Compiler

-- TODO (Issue #18): safer code and better tests for this module

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

toPlonkConstaint :: Polynomial F -> (F, F, F, F, F, F, F, F)
toPlonkConstaint p =
    let xs    = nubOrd $ concatMap (keys . getPowers) (getMonomials p)
        i     = order @F
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0         -> [i, i, i]
            1         -> [i, i, head xs, head xs]
            2         -> [i] ++ xs ++ xs
            _         -> xs ++ xs

        getCoef :: Map Integer (Var F Integer) -> F
        getCoef m = case find (\(M _ as) -> m == as) (getMonomials p) of
            Just (M c _) -> c
            _            -> zero

        getCoefs :: [Integer] -> Maybe (F, F, F, F, F, F, F, F)
        getCoefs [a, b, c] = do
            let xa = fromList [(a, Var 1)]
                xb = fromList [(b, Var 1)]
                xc = fromList [(c, Var 1)]
                xaxb = fromList [(a, Var 1), (b, Var 1)]

                ql = getCoef xa
                qr = getCoef xb
                qo = getCoef xc
                qm = getCoef xaxb
                qc = getCoef empty
            guard $ p - polynomial [M ql xa, M qr xb, M qo xc, M qm xaxb, M qc empty] == zero
            return (ql, qr, qo, qm, qc, toZp a, toZp b, toZp c)
        getCoefs _ = Nothing

    in head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (F, F, F, F, F, F, F, F) -> Polynomial F
fromPlonkConstraint (ql, qr, qo, qm, qc, a, b, c) =
    let xa = fromList [(fromZp a, Var 1)]
        xb = fromList [(fromZp b, Var 1)]
        xc = fromList [(fromZp c, Var 1)]
        xaxb = fromList [(fromZp a, Var 1), (fromZp b, Var 1)]

    in polynomial [M ql xa, M qr xb, M qo xc, M qm xaxb, M qc empty]

addPublicInput :: Integer -> F -> [Polynomial F] -> [Polynomial F]
addPublicInput i _ ps =
    polynomial [M one (fromList [(i, Var 1)])] : ps

addPublicInputs :: Map Integer F -> [Polynomial F] -> [Polynomial F]
addPublicInputs inputs ps = foldr (\(i, x) ps' -> addPublicInput i x ps') ps $ toList inputs

removeConstantVariable :: Polynomial F -> Polynomial F
removeConstantVariable p =
    polynomial . map (\(M c as) -> M c (0 `delete` as)) $ getMonomials p

toPlonkArithmetization :: forall a . Finite a => Map Integer F -> ArithmeticCircuit F
    -> (PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a)
toPlonkArithmetization inputs ac =
    let f (x0, x1, x2, x3, x4, x5, x6, x7) = [x0, x1, x2, x3, x4, x5, x6, x7]
        vars    = nubOrd $ sort $ 0 : concatMap (keys . getPowers) (concatMap getMonomials $ acSystem ac)
        ac'     = mapVarArithmeticCircuit ac
        inputs' = mapVarWitness vars inputs
        system  = addPublicInputs inputs' $ elems $ acSystem ac'

    in case map toPolyVec $ transpose $ map (f . toPlonkConstaint . removeConstantVariable) system of
            [ql, qr, qo, qm, qc, a, b, c] -> (ql, qr, qo, qm, qc, a, b, c)
            _                             -> error "toPlonkArithmetization: something went wrong"