{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Algorithm.ReedSolomon where


import           Data.Bifunctor                             (bimap)
import           Data.Bool                                  (bool)
import           Data.Vector                                as V
import           GHC.Natural                                (Natural)
import           Prelude                                    (Eq, Int, Integer, Maybe (..), Num (fromInteger), error,
                                                             fromIntegral, id, ($), (.), (<=), (==))
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

generator :: (Field a, Eq a) => Int -> a -> Poly a
generator r a = V.foldr (\ai pi -> toLinPoly ai * pi) one roots
    where
        roots = V.iterateN r (* a) a
        toLinPoly p = toPoly $ fromList [negate p, one]

encode :: (Field c, Eq c) => [c] -> c -> Int -> Poly c
encode msg prim_elem r = msg_padded - reminder
    where
        g_x = generator r prim_elem
        poly_msg = toPoly $ fromList msg
        msg_padded = scaleP one (fromIntegral r) poly_msg
        (_, reminder) = qr msg_padded g_x

-- beta = one
decode :: (Field c, Eq c) => Poly c -> c -> Int -> Int  -> Poly c
decode encoded primeElement fieldOrd r = bool decoded encoded' isCorrect
    where
        fieldElements = iterateN fieldOrd (* primeElement) primeElement

        encoded' = toPoly . V.drop r $ fromPoly encoded
        syndromes = toPoly . V.map (evalPoly encoded) $ take r fieldElements
        isCorrect = zero == syndromes

        (_, lx) = berlekamp syndromes r

        es1 = V.indexed $ V.iterateN fieldOrd (* primeElement) one

        iroots = mapMaybe (\(i,x) -> bool Nothing (Just (fieldOrd P.- i , x)) (evalPoly lx x == zero)) es1

        omega = toPoly $ take r $ fromPoly (lx * syndromes)
        lx'= diff lx

        err = V.foldl (+) zero $ map (\(i,x) ->
            let xi = bool (monomial (fromIntegral i) one) (constant one) (i == fieldOrd)
                ei = negate $ evalPoly omega x * finv (evalPoly lx' x)
            in constant ei * xi) iroots

        fx = encoded - err
        checkSum = V.map (evalPoly fx) $ V.take r fieldElements

        decoded = bool (error "Can't decode") (toPoly $ V.drop r $ fromPoly fx) (all (== zero) checkSum)


berlekamp :: forall c . (Field c, Eq c) => Poly c -> Int -> (Integer, Poly c)
berlekamp s r
    | deg s == -1 = (0, one)
    | P.otherwise = go сx0 bx0 0 0 1 one
    where
        sv = fromPoly s
        сx0 = one :: Poly c
        bx0 = one :: Poly c
        lenS = fromIntegral r

        go :: Poly c -> Poly c -> Integer -> Integer -> Natural -> c -> (Integer, Poly c)
        go cx bx n l m b
            | n == lenS = bool (error "locators didn't find") (l, cx) (deg cx == l)
            | P.otherwise = bool innerChoice (go cx bx n' l (m+1) b) (d == zero)
            where
                d = scalarN (fromIntegral n P.+ 1) (l+1) lxv sv

                lxv = fromPoly cx
                cx' = cx - fromConstant d * constant (finv b) * bx * monomial m one

                n' = n + 1
                innerChoice = bool (go cx' bx n' l (m+1) b) (go cx' cx n' (n+1-l) 1 d) (2*l <= n)


scalarN :: (Semiring c) => Int -> Integer -> Vector c -> Vector c -> c
scalarN q l lv rv = V.foldl (+) zero $ V.take (fromInteger l) $ V.zipWith (*) lPadded rPadded
    where
        lPadded = lv V.++ V.replicate (q P.- V.length lv) zero
        rPadded = V.reverse $ V.take q $ rv V.++ V.replicate (q P.- V.length rv) zero


diff :: ( Field c, Eq c) =>Poly c -> Poly c
diff p = let cs = fromPoly p in toPoly $ V.tail $ V.imap (\i c -> scale (fromIntegral i :: Integer) c) cs
