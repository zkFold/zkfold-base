module ZkFold.Crypto.EllipticCurve.Class where


import Prelude (Bool, Int)
import Data.List (zipWith, foldl1', length) 
import ZkFold.Crypto.Algebra.Class

newtype BaseField curve = BaseField curve
newtype ScalarField curve = ScalarField curve
newtype Polynomial field = Polynomial [field]

-- instance MultiplicativeSemigroup (Polynomial field) where
--     {-# INLINABLE (*) #-}
--     (*) x y = Polynomial $ zipWith0 (*) x' y'
--         where Polynomial x' = x
--               Polynomial y' = y

evaluate:: EllipticCurve curve => Polynomial (ScalarField curve) -> BaseField curve
evaluate (Polynomial coefs) = foldl1' add (zipWith mul coefs (powers_of_g (length coefs)))

class EllipticCurve curve where
    on_curve :: BaseField curve  -> Bool
    generator :: BaseField curve 
    powers_of_g :: Int -> [BaseField curve] 

    add :: BaseField curve -> BaseField curve -> BaseField curve
    mul :: ScalarField curve -> BaseField curve -> BaseField curve

-- | Curve point addition.
pointAdd:: EllipticCurve curve => BaseField curve -> BaseField curve -> BaseField curve
pointAdd = add

-- | Curve point multiplication.
pointMult:: EllipticCurve curve => ScalarField curve -> BaseField curve -> BaseField curve
pointMult = mul