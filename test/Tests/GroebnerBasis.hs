{-# LANGUAGE TypeApplications    #-}

module Tests.GroebnerBasis (testGroebner) where

import           Prelude                                     hiding (not, Num(..), Eq(..), (^), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis

import           Tests.Utility.Types (SmallField)

testPoly :: Prime p => [Polynomial p]
testPoly = map polynomial [
        [monomial 1 [1, 1, 0], monomial 1 [1, 1, 1]],
        [monomial 1 [0, 1, 0], monomial 1 [0, 0, 1]],
        [monomial 1 [1, 0, 0], monomial 1 [1, 0, 1]]
    ]

testGroebner :: IO ()
testGroebner = do
    putStrLn "\nStarting Groebner test...\n"

    putStrLn "Test system:"
    print $ testPoly @SmallField
    putStrLn ""

    putStrLn "Zero tests:"
    print $ zeroM $ monomial @SmallField zero [1, 2, 3]
    print $ zeroP $ polynomial @SmallField [monomial zero [1, 2, 3], monomial zero [1, 2, 3]]
    putStrLn ""

    putStrLn "Similarity test:"
    print $ similarM (monomial @SmallField zero [1, 2, 3]) (monomial one [1, 2, 3])
    putStrLn ""

    putStrLn "Comparison tests:"
    print $ compare (monomial @SmallField zero [1, 3, 2]) (monomial one [1, 2, 3])
    print $ compare (monomial @SmallField one [1, 0, 1]) (monomial one [1, 1, 1])
    print $ compare 
        (polynomial [monomial @SmallField one [1, 0, 1], monomial one [1, 1, 1]])
        (polynomial [monomial one [1, 1, 1], monomial one [1, 0, 1]])
    putStrLn ""

    putStrLn "Polynomial multiplication:"
    print $ (testPoly @SmallField !! 0) * (testPoly !! 1)
    putStrLn ""

    putStrLn "Leading terms:"
    mapM_ (print . lt . (testPoly @SmallField !!)) [0..2]
    putStrLn ""

    putStrLn "Constructing S-polynomial:"
    print $ makeSPoly (testPoly @SmallField !! 0) (testPoly !! 1)
    putStrLn ""

    putStrLn "Groebner basis:"
    print $ groebner @SmallField testPoly