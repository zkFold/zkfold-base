{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Protocol.Commitment.KZG where

import Data.Poly
import ZkFold.Crypto.EllipticCurve.Class (EllipticCurve (powers_of_g), generator, mul, add, evaluate, BaseField, ScalarField, Polynomial)

-- class Polynomial scalar where
--     coefs :: [scalar]

--     mulByScalar :: scalar -> ()

--     derive :: Polynomial scalar -> ()


class KZG g1 g2 where
    commitment :: Polynomial (ScalarField g1) -> BaseField g1

    whitness :: ScalarField g1 -> BaseField g1


instance (EllipticCurve g1, EllipticCurve g2) => KZG g1 g2 where
    commitment poly = evaluate poly

    whitness _ = generator