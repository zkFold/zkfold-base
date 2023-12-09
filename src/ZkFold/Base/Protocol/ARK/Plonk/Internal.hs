{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.ARK.Plonk.Internal where

import           Control.Monad                                         (guard)
import           Data.Containers.ListUtils                             (nubOrd)
import           Data.List                                             (permutations, sort, find, transpose)
import           Data.Map                                              (Map, keys, fromList, empty, mapKeys)
import           Data.Maybe                                            (mapMaybe)
import           Prelude                                               hiding (Num(..), (^), (/), (!!), sum, length, take, drop)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                       (toZp, fromZp)
import           ZkFold.Base.Algebra.Basic.Permutations                (Permutation (..), mkIndexPartition, fromCycles)
import           ZkFold.Base.Algebra.Polynomials.Univariate            (PolyVec, toPolyVec, fromPolyVec)
import           ZkFold.Base.Algebra.Polynomials.Multivariate          (Polynomial, Monomial, getMonomials, getPowers, polynomial)
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Internal (Polynom(..), Monom(..), Var(..))
import           ZkFold.Base.Protocol.Commitment.KZG
import           ZkFold.Prelude                                        (take, length, drop, elemIndex)

-- TODO: safe code

mapVariables :: [Polynomial F] -> [Polynomial F]
mapVariables ps = map mapVarPolynomial ps
    where
        vars = concatMap (keys . getPowers) $ concatMap getMonomials ps

        mapVar :: Integer -> Integer
        mapVar x = case x `elemIndex` vars of
            Just i  -> i
            Nothing -> error "mapVariables: something went wrong"

        mapVarMonomial :: Monomial F -> Monomial F
        mapVarMonomial (M c as) = M c $ mapKeys mapVar as

        mapVarPolynomial :: Polynomial F -> Polynomial F
        mapVarPolynomial (P ms) = P $ map mapVarMonomial ms

toPlonkConstaint :: Polynomial F -> (F, F, F, F, F, F, F, F)
toPlonkConstaint p =
    let xs    = concatMap (keys . getPowers) (getMonomials p)
        perms = map (nubOrd . sort . take 3) $ permutations $ case length xs of
            0         -> [0, 0, 0]
            1         -> [0, 1, 1]
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

toPlonkArithmetization :: forall a . Finite a => [Polynomial F]
    -> (PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a,
    PolyVec F a, PolyVec F a, PolyVec F a)
toPlonkArithmetization ps =
    let f (x0, x1, x2, x3, x4, x5, x6, x7) = [x0, x1, x2, x3, x4, x5, x6, x7]

    in case map toPolyVec $ transpose $ map (f . toPlonkConstaint) $ mapVariables ps of
            [ql, qr, qo, qm, qc, a, b, c] ->
                let Permutation s = fromCycles @a $ mkIndexPartition $ map fromZp $ fromPolyVec a ++ fromPolyVec b ++ fromPolyVec c
                    s1   = toPolyVec $ map toZp $ take (order @a) s
                    s2   = toPolyVec $ map toZp $ take (order @a) $ drop (order @a) s
                    s3   = toPolyVec $ map toZp $ take (order @a) $ drop (2 * order @a) s
                in (ql, qr, qo, qm, qc, s1, s2, s3)
            _                             -> error "toPlonkArithmetization: something went wrong"