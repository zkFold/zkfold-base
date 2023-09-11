module ZkFold.Crypto.EllipticCurve.Class where

import Prelude (Integer, Bool)

newtype Point curve = Point Integer

class EllipticCurve curve where
    on_curve :: Point curve -> Bool
    generator :: Point curve

    add :: Point curve -> Point curve -> Point curve
    mult :: Point curve -> Point curve -> Point curve


-- | Curve point addition.
pointAdd:: EllipticCurve curve => Point curve -> Point curve -> Point curve
pointAdd = add

-- | Curve point multiplication.
pointMult:: EllipticCurve curve => Point curve -> Point curve -> Point curve
pointMult = mult