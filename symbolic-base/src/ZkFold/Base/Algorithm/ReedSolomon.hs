{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Algorithm.ReedSolomon where


import           Data.Bool                                  (bool)
import           Data.Vector                                as V
import           GHC.Natural                                (Natural)
import           Prelude                                    (Eq, Integer, Integral (toInteger), Num (fromInteger),
                                                             error, fromIntegral, iterate, length, map, unzip, ($),
                                                             (/=), (<), (==), Int)
import qualified Prelude                                    as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field            (Zp)
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, value)
import           ZkFold.Base.Algebra.Polynomials.Univariate


type RSField p = Zp p

data RSParams c i j = ReedSolomonParams
    { fullLength   :: Natural
    , usefulLength :: Natural
    , bitsPerBlock :: Natural
    }

numberOfError :: forall n k. (KnownNat n, KnownNat k) => Natural
numberOfError = (value @n -! value @k) `div` 2

generator :: (Field a, Eq a) => Int -> Int -> a -> Poly a
generator n k a = V.foldr (\ai pi -> toLinPoly ai * pi) one roots
    where
        dif = n P.- k
        roots = V.iterateN dif (* a) a
        toLinPoly p = toPoly $ fromList [negate p, one]

encode :: (Field c, Eq c) => [c] -> c -> Int -> Int -> Poly c
encode msg prim_elem n k = msg_padded - remainder
    where
        a = prim_elem
        g_x = generator n k a
        poly_msg = toPoly $ fromList msg
        msg_padded = scaleP one (fromIntegral $ n P.- k) poly_msg
        (_, remainder) = qr msg_padded g_x

-- beta = one
decoder :: (Field c, Eq c, MultiplicativeGroup c) => Poly c -> c -> Natural -> Natural -> Poly c
decoder encoded prim_elem n k = bool decoded encoded' isCorrect
    where
        fieldElements = V.snoc (V.takeWhile (/= one) $  V.fromList $ iterate (* prim_elem) prim_elem) one
        fieldOrd = toInteger $ V.length fieldElements
        elementsWithLog = V.zip fieldElements (V.generate (fromIntegral fieldOrd) fromIntegral)

        e = fromPoly encoded
        encoded' = toPoly $ V.take (fromIntegral k) e
        dif = fromIntegral $ n -! k
        syndromes = toPoly $ V.map (evalPoly encoded) $ V.take dif fieldElements
        isCorrect = zero == syndromes

        (l, lx) = berlekamp syndromes

        (ul', xs) = Prelude.unzip $ foldr (\(fElem, ePow) otherRoots -> bool otherRoots ((fieldOrd - ePow, fElem) : otherRoots) (evalPoly lx fElem == zero)) [] elementsWithLog
        ul = bool (error "mistakes are incorrigible") ul' (Prelude.length ul' /= fromIntegral (deg lx))

        omega = foldr (\q p -> let pxv = fromPoly lx
                                   sv = V.reverse $ fromPoly syndromes
                                   xq = monomial (fromIntegral q) one
                                in xq * constant (scalarMulN q pxv sv) + p) zero (V.fromList [0..l-1])
        lxDiff = diff lx

        vl = Prelude.map (\x -> evalPoly omega x / evalPoly lxDiff x) xs

        ex = P.foldl (+) zero $ P.zipWith (\vi li -> constant vi * monomial (fromIntegral li) one) vl ul

        fx = encoded + ex
        checkSum = V.map (evalPoly fx) $ V.take dif fieldElements

        decoded = bool (error "mistakes are incorrigible") fx (all (== zero) checkSum)


berlekamp :: forall c . (Field c, Eq c) => Poly c -> (Integer, Poly c)
berlekamp s = if deg s == 1 then (0, one) else go lx0 bx0 0 0 (-1)
    where
        lx0 = one :: Poly c
        bx0 = one :: Poly c
        lenS = fromInteger $ deg s + 1

        go :: Poly c -> Poly c -> Integer -> Integer -> Integer -> (Integer, Poly c)
        go lx bx q l m = if q == lenS
            then (l, lx)
            else bool innerChoice (go lx bx' q' l m) (d == zero)
                where
                    d = scalarMulN (l + 1) (fromPoly lx) (V.reverse $ fromPoly s)

                    lx' = lx + fromConstant d * bx

                    bx' = monomial 1 one * bx
                    bx'' = monomial 1 one * fromConstant (finv d) * bx

                    q' = q + 1

                    innerChoice = bool (go lx' bx' q' l m) (go lx' bx'' q' (q-m) (q-l)) (l < q - m)


scalarMulN :: (AdditiveMonoid c) => Integer -> V.Vector c -> V.Vector c -> c
scalarMulN n lv rv = V.foldl (+) zero $ V.take (fromInteger n) $ V.zipWith (+) lv rv