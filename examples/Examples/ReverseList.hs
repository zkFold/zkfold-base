{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Examples.ReverseList (exampleReverseList) where

import           Data.FixedLength                            (indices, toList, index, map)
import           Prelude                                     hiding (Num(..), Eq(..), (^), (/), (!!), (||), zipWith, not, any, map)
import           Type.Data.Num.Unary                         (Natural)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              ((!!), writeFileJSON)
import           ZkFold.Symbolic.Arithmetization             (ArithmeticCircuit, acSizeM, acSizeN)
import           ZkFold.Symbolic.Compiler                    (compile)
import           ZkFold.Symbolic.Data.List                   (List, U32, lengthList, indicesInteger)

type X a = (a, a)

-- | Reverses the order of elements in a fixed size list
-- NOTE: With our approach a list can be inverted for free!
-- Compare this to the "Reverse Array" example from the Polylang playground
-- https://polylang.dev/playground 
reverseList :: forall a n . (Natural n) => List n (X a) -> List n (X a)
reverseList lst = map (`index` lst) (map (toList indices !!) inds)
    where
        inds = map f indicesInteger
        f i = lengthList @n - 1 - i

exampleReverseList :: IO ()
exampleReverseList = do

    let acs   = toList @U32 (compile @(Zp BLS12_381_Scalar) (reverseList @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @U32))
                    :: [X (ArithmeticCircuit (Zp BLS12_381_Scalar))]
        ac    = fst $ head acs
        file = "compiled_scripts/reverseList.json"

    putStrLn "\nExample: Reverse List function\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: "   ++ show (acSizeM ac)
    writeFileJSON file ac
    putStrLn $ "Script saved: " ++ file