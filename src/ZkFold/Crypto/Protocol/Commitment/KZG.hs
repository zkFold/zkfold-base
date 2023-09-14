{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Protocol.Commitment.KZG where

import Data.Poly
import ZkFold.Crypto.EllipticCurve.Class (EllipticCurve, generator, BaseField)

-- class Polynomial scalar where
--     coefs :: [scalar]

--     mulByScalar :: scalar -> ()

--     derive :: Polynomial scalar -> ()


class KZG g1 g2 where
    commitment :: BaseField g1

    whitness :: BaseField g1


instance (EllipticCurve g1, EllipticCurve g2) => KZG g1 g2 where
    commitment = generator

    whitness = generator