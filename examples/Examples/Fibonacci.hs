{-# LANGUAGE TypeApplications #-}

module Examples.Fibonacci (exampleFibonacci) where

import           Data.Foldable                     (foldl)
import           Prelude                           (Integer)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.Conditional  (bool)
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)

-- | The Fibonacci index function.
-- If `x` is a Fibonacci number, returns its index (up until `nMax`).
-- Otherwise, returns `0`.
exampleFibonacci ::
  forall c. Symbolic c => Integer -> FieldElement c -> FieldElement c
exampleFibonacci nMax x =
  foldl
    (\m k -> bool @(Bool c) m (fromConstant k) (fib k one one == x))
    zero
    [1..nMax]
    where
        fib :: Integer -> FieldElement c -> FieldElement c -> FieldElement c
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)
