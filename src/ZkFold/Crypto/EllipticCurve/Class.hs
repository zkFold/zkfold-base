module ZkFold.Crypto.EllipticCurve.Class where


import Prelude (Bool)

newtype BaseField curve = BaseField curve
newtype ScalarField curve = ScalarField curve

class EllipticCurve curve where
    on_curve :: BaseField curve  -> Bool
    generator :: BaseField curve 

    add :: BaseField curve -> BaseField curve -> BaseField curve
    mul :: ScalarField curve -> BaseField curve -> BaseField curve

-- | Curve point addition.
pointAdd:: EllipticCurve curve => BaseField curve -> BaseField curve -> BaseField curve
pointAdd = add

-- | Curve point multiplication.
pointMult:: EllipticCurve curve => ScalarField curve -> BaseField curve -> BaseField curve
pointMult = mul