{-# LANGUAGE TypeApplications #-}

module Main where

import           Prelude                                      hiding (Num(..), Fractional(..), length)

import           Tests.Arithmetization                       (specArithmetization)
import           Tests.Field                                 (specField)
import           Tests.GroebnerBasis                         (specGroebner)

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr, Fq, Fq2, Fq6, Fq12)

main :: IO ()
main = do
    specField @Fr
    specField @Fq
    specField @Fq2
    specField @Fq6
    specField @Fq12
    specArithmetization
    specGroebner