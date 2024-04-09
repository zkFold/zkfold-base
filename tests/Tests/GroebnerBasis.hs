{-# LANGUAGE TypeApplications #-}

module Tests.GroebnerBasis (specGroebner) where

import Data.Map (fromList)
import Test.Hspec
import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Number (Prime)
import ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import ZkFold.Symbolic.GroebnerBasis
import Prelude hiding (Eq (..), Num (..), (/), (^))

testPoly :: (Prime p) => [Polynomial p]
testPoly =
  map
    polynomial
    [ [ monomial 1 (fromList [(1, variable 1), (2, variable 1)]),
        monomial 1 (fromList [(1, variable 1), (2, variable 1), (3, variable 1)])
      ],
      [ monomial 1 (fromList [(2, variable 1)]),
        monomial 1 (fromList [(3, variable 1)])
      ],
      [ monomial 1 (fromList [(1, variable 1)]),
        monomial 1 (fromList [(1, variable 1), (3, variable 1)])
      ]
    ]

specGroebner :: IO ()
specGroebner = hspec $ do
  describe "Groebner basis specification" $ do
    describe "Monomial zero test" $ do
      it "should pass" $ do
        zeroM (monomial @(Order Fr) zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
          `shouldBe` True
    describe "Polynomial zero test" $ do
      it "should pass" $ do
        zeroP
          ( polynomial @(Order Fr)
              [ monomial zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)],
                monomial zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)]
              ]
          )
          `shouldBe` True
    describe "Similar monomials" $ do
      it "should be equal" $ do
        similarM
          (monomial @(Order Fr) zero $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
          (monomial one $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
          `shouldBe` True
    describe "Monomials comparisons" $ do
      it "should be correct" $ do
        compare
          (monomial @(Order Fr) zero $ fromList [(1, variable 1), (2, variable 3), (3, variable 2)])
          (monomial one $ fromList [(1, variable 1), (2, variable 2), (3, variable 3)])
          `shouldBe` LT
        compare
          (monomial @(Order Fr) one $ fromList [(1, variable 1), (3, variable 1)])
          (monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)])
          `shouldBe` LT
        compare
          ( polynomial
              [ monomial @(Order Fr) one $ fromList [(1, variable 1), (2, variable 1)],
                monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)]
              ]
          )
          ( polynomial
              [ monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)],
                monomial one $ fromList [(1, variable 1), (3, variable 1)]
              ]
          )
          `shouldBe` GT
    describe "Polynomial multiplication test" $ do
      it "should pass" $ do
        (testPoly @(Order Fr) !! 0) * (testPoly !! 1)
          `shouldBe` polynomial
            [ monomial one $ fromList [(1, variable 1), (2, variable 2), (3, variable 1)],
              monomial one $ fromList [(1, variable 1), (2, variable 2)],
              monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 2)],
              monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)]
            ]
    describe "Leading term test" $ do
      it "should pass" $ do
        map (lt . (testPoly @(Order Fr) !!)) [0 .. 2]
          `shouldBe` [ monomial one $ fromList [(1, variable 1), (2, variable 1), (3, variable 1)],
                       monomial one $ fromList [(2, variable 1)],
                       monomial one $ fromList [(1, variable 1), (3, variable 1)]
                     ]
    describe "S-polynomial test" $ do
      it "should pass" $ do
        let s = makeSPoly (testPoly @(Order Fr) !! 0) (testPoly !! 1)
        s
          `shouldBe` polynomial
            [ monomial one $ fromList [(1, variable 1), (2, variable 1)],
              monomial (negate one) $ fromList [(1, variable 1), (3, variable 2)]
            ]
        s `fullReduceMany` [testPoly !! 2]
          `shouldBe` polynomial
            [ monomial one $ fromList [(1, variable 1), (2, variable 1)],
              monomial (negate one) $ fromList [(1, variable 1)]
            ]
    describe "Groebner basis test" $ do
      it "should pass" $ do
        let p0 = polynomial @(Order Fr) [monomial one $ fromList [(1, variable 1)]]
            gs = snd $ foldl (\args _ -> uncurry groebnerStep args) (p0, testPoly) [1 :: Integer .. 200]
            gs' = filter (not . zeroP) $ foldr (\p ps -> fullReduceMany p ps : ps) [] gs
        gs'
          `shouldBe` [ polynomial
                         [ monomial one $ fromList [(2, variable 1)],
                           monomial one $ fromList [(3, variable 1)]
                         ],
                       polynomial
                         [ monomial one $ fromList [(1, variable 1), (3, variable 1)],
                           monomial one $ fromList [(1, variable 1)]
                         ]
                     ]
