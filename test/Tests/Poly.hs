{-# LANGUAGE TypeApplications    #-}

module Tests.Poly (testPoly) where

import           Prelude                                    hiding (not, Num(..), Eq(..), (^), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Polynomials.Poly

import           Tests.Utility.Types                        (SmallField)
import           ZkFold.Crypto.Algebra.Basic.Field (Zp)

samplePoly :: Prime p => Poly (Zp p)
samplePoly = P [1, 2 ,3]

testPoly :: IO ()
testPoly = do
    putStrLn "\nStarting Poly test...\n"

    putStrLn "Sample Poly: "
    print $ samplePoly @SmallField

    let l = P @(Zp SmallField) [1, 2, 3]
    let r = P @(Zp SmallField) [3, 2, 1]
    putStrLn "Polys l and r:"
    print l
    print r

    putStrLn "\nPoly addition:"
    putStrLn "l + r = "
    print $ l + r


    putStrLn "\nPoly multiplication:"
    putStrLn "l + r = "
    print $ l * r