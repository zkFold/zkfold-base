{-# LANGUAGE OverloadedLists  #-}
{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Protocol.ARK.Plonk.Internal where

import           Control.Monad                                (guard)
import           Data.Bifunctor                               (first)
import           Data.Bool                                    (bool)
import           Data.Containers.ListUtils                    (nubOrd)
import           Data.List                                    (find, permutations, sort, transpose)
import           Data.Map                                     (Map, elems, empty)
import           Data.Maybe                                   (mapMaybe)
import qualified Data.Vector                                  as V
import           GHC.IsList                                   (IsList (..))
import           Numeric.Natural                              (Natural)
import           Prelude                                      hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           System.Random                                (RandomGen, mkStdGen, uniformR)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field              (fromZp)
import           ZkFold.Base.Algebra.Basic.Number             (KnownNat)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381  (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate (Polynomial', evalMapM, evalPolynomial, mapVar,
                                                               polynomial, var, variables)
import           ZkFold.Base.Algebra.Polynomials.Univariate   (PolyVec, toPolyVec)
import           ZkFold.Prelude                               (length, take)
import           ZkFold.Symbolic.Compiler

type F = ScalarField BLS12_381_G1
type G1 = Point BLS12_381_G1
type G2 = Point BLS12_381_G2

-- TODO (Issue #15): safer code and better tests for this module

getParams :: Natural -> (F, F, F)
getParams l = findK' $ mkStdGen 0
    where
        omega = case rootOfUnity l of
                  Just o -> o
                  _      -> error "impossible"
        hGroup = map (omega^) [1 .. 2^l-!1]
        hGroup' k = map (k*) hGroup

        findK' :: RandomGen g => g -> (F, F, F)
        findK' g =
            let (k1, g') = first fromConstant $ uniformR (1, order @F -! 1) g
                (k2, g'') = first fromConstant $ uniformR (1, order @F -! 1) g'
            in bool (findK' g'') (omega, k1, k2) $
                all (`notElem` hGroup) (hGroup' k1)
                && all (`notElem` hGroup' k1) (hGroup' k2)

toPlonkConstraint :: Polynomial' F -> (F, F, F, F, F, F, F, F)
toPlonkConstraint p =
    let xs    = toList $ variables p
        i     = order @F
        perms = nubOrd $ map (take 3) $ permutations $ case length xs of
            0 -> [i, i, i]
            1 -> [i, i, head xs, head xs]
            2 -> [i] ++ xs ++ xs
            _ -> xs ++ xs

        getCoef :: Map Natural Natural -> F
        getCoef m = case find (\(_, as) -> m == as) (toList p) of
            Just (c, _) -> c
            _           -> zero

        getCoefs :: [Natural] -> Maybe (F, F, F, F, F, F, F, F)
        getCoefs [a, b, c] = do
            let xa = [(a, 1)]
                xb = [(b, 1)]
                xc = [(c, 1)]
                xaxb = [(a, 1), (b, 1)]

                ql = getCoef $ fromList xa
                qr = getCoef $ fromList xb
                qo = getCoef $ fromList xc
                qm = getCoef $ fromList xaxb
                qc = getCoef $ empty
            guard $ p - polynomial [(ql, fromList xa), (qr, fromList xb), (qo, fromList xc), (qm, fromList xaxb), (qc, one)] == zero
            return (ql, qr, qo, qm, qc, fromConstant a, fromConstant b, fromConstant c)
        getCoefs _ = Nothing

    in head $ mapMaybe getCoefs perms

fromPlonkConstraint :: (F, F, F, F, F, F, F, F) -> Polynomial' F
fromPlonkConstraint (ql, qr, qo, qm, qc, a, b, c) =
    let xa = [(fromZp a, 1)]
        xb = [(fromZp b, 1)]
        xc = [(fromZp c, 1)]
        xaxb = [(fromZp a, 1), (fromZp b, 1)]

    in polynomial [(ql, xa), (qr, xb), (qo, xc), (qm, xaxb), (qc, one)]

addPublicInput :: Natural -> [Polynomial' F] -> [Polynomial' F]
addPublicInput i ps = var i : ps

removeConstantVariable :: (Eq c, Field c, Scale c c, FromConstant c c) => Polynomial' c -> Polynomial' c
removeConstantVariable = evalPolynomial evalMapM (\x -> if x == 0 then one else var x)

toPlonkArithmetization :: forall a . KnownNat a => V.Vector Natural -> ArithmeticCircuit F
    -> (PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a, PolyVec F a)
toPlonkArithmetization ord ac =
    let f (x0, x1, x2, x3, x4, x5, x6, x7) = [x0, x1, x2, x3, x4, x5, x6, x7]
        vars   = nubOrd $ sort $ 0 : concatMap (toList . variables) (elems $ acSystem ac)
        ac'    = mapVarArithmeticCircuit ac
        inputs = fmap (mapVar vars) ord
        system = foldr addPublicInput (elems $ acSystem ac') inputs

    in case map (toPolyVec . V.fromList) $ transpose $ map (f . toPlonkConstraint . removeConstantVariable) system of
            [ql, qr, qo, qm, qc, a, b, c] -> (ql, qr, qo, qm, qc, a, b, c)
            _                             -> error "toPlonkArithmetization: something went wrong"
