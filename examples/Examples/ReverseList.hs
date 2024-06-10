{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Examples.ReverseList (exampleReverseList) where

import           Prelude

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler

-- | Reverses the order of elements in a vector
reverseList :: forall t n . Vector n t -> Vector n t
reverseList (Vector as) = Vector $ reverse as

exampleReverseList :: IO ()
exampleReverseList = do
    let file = "compiled_scripts/reverseList.json"

    putStrLn "\nExample: Reverse List function\n"

    compileIO @(Zp BLS12_381_Scalar) file (reverseList @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @32)

