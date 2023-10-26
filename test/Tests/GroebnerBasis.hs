{-# LANGUAGE TypeApplications    #-}

module Tests.GroebnerBasis (testGroebner) where

import           Data.Bool                                  (not)
import           Data.Map                                   (fromList)
import           Prelude                                    hiding (not, Num(..), Eq(..), (^), (/))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.GroebnerBasis

import           Tests.Utility.Types                        (SmallField)

testPoly :: Prime p => [Polynomial p]
testPoly = map polynomial [
        [monomial 1 (fromList [(1, variable 1), (2, variable 1)]),
         monomial 1 (fromList [(1, variable 1), (2, variable 1), (3, variable 1)])],
        [monomial 1 (fromList [(2, variable 1)]),
         monomial 1 (fromList [(3, variable 1)])],
        [monomial 1 (fromList [(1, variable 1)]),
         monomial 1 (fromList [(1, variable 1), (3, variable 1)])]
    ]

testGroebner :: IO ()
testGroebner = do
    putStrLn "\nStarting Groebner test...\n"

    putStrLn "Test system:"
    print $ testPoly @SmallField
    putStrLn ""

    putStrLn "Zero tests:"
    print $ zeroM $ monomial @SmallField zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)]
    print $ zeroP $ polynomial @SmallField [monomial zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)],
        monomial zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)]]
    putStrLn ""

    putStrLn "Similarity test:"
    print $ similarM (monomial @SmallField zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
        (monomial one $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
    putStrLn ""

    putStrLn "Comparison tests:"
    print $ compare (monomial @SmallField zero $ fromList [(1, variable 1), (2, variable 3), (3, variable 2)])
        (monomial one $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
    print $ compare (monomial @SmallField one $ fromList [(1, variable 1), (3, variable 1)])
        (monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)])
    print $ compare 
        (polynomial [monomial @SmallField one $ fromList [(1, variable 1), (2, variable 1)],
            monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)]])
        (polynomial [monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)],
            monomial one $ fromList [(1, variable 1), (3, variable 1)]])
    putStrLn ""

    putStrLn "Polynomial multiplication:"
    print $ (testPoly @SmallField !! 0) * (testPoly !! 1)
    putStrLn ""

    putStrLn "Leading terms:"
    mapM_ (print . lt . (testPoly @SmallField !!)) [0..2]
    putStrLn ""

    putStrLn "Constructing S-polynomial:"
    let s = makeSPoly (testPoly @SmallField !! 0) (testPoly !! 1)
    print s
    putStrLn "Reducing..."
    print $ s `fullReduceMany` [testPoly !! 2]
    putStrLn ""

    let p0 = polynomial @SmallField [monomial one $ fromList [(1, variable 1)]]
        gs = snd $ foldl (\args _ -> uncurry groebnerStep args) (p0, testPoly) [1::Integer ..200] 
        gs' = filter (not . zeroP) $ foldr (\p ps -> fullReduceMany p ps : ps) [] gs

    putStrLn "Groebner basis:"
    print gs
    putStrLn "Reducing..."
    print gs'