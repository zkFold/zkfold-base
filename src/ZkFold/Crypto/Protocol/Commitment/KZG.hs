{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Protocol.Commitment.KZG where

import ZkFold.Crypto.EllipticCurve.Class (EllipticCurve (powers_of_g), generator, mul, add, evaluate, BaseField, ScalarField)
import ZkFold.Crypto.Algebra.Polynomials.Poly

-- class Polynomial scalar where
--     coefs :: [scalar]

--     mulByScalar :: scalar -> ()

--     derive :: Polynomial scalar -> ()


class KZG g1 g2 where
    commitment :: Poly (ScalarField g1) -> BaseField g1

    whitness :: ScalarField g1 -> BaseField g1


instance (EllipticCurve g1, EllipticCurve g2) => KZG g1 g2 where
    commitment poly = evaluate poly

    whitness _ = generator