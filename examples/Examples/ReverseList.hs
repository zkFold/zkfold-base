{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Examples.ReverseList (exampleReverseList) where

import           Data.FixedLength                            (indices, toList, index, map)
import           Prelude                                     hiding (Num(..), Eq(..), (^), (/), (!!), (||), zipWith, not, any, map)
import           Type.Data.Num.Unary                         (Natural)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              ((!!))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.List                   (List, U32, lengthList, indicesInteger)

type X a = (a, a)

-- | Reverses the order of elements in a fixed size list
reverseList :: forall a n . (Natural n) => List n (X a) -> List n (X a)
reverseList lst = map (`index` lst) (map (toList indices !!) inds)
    where
        inds = map f indicesInteger
        f i = lengthList @n - 1 - i

exampleReverseList :: IO ()
exampleReverseList = do
    let file = "compiled_scripts/reverseList.json"

    putStrLn "\nExample: Reverse List function\n"

    compileIO @(Zp BLS12_381_Scalar) file (reverseList @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @U32)