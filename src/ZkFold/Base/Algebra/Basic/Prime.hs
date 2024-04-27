{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.Prime (
    Prime, KnownPrime, IsPrime, Divides
) where

import           Data.Kind
import           Data.Type.Bool
import           GHC.TypeLits
import           Prelude

class KnownNat p => Prime p where

-- Use this overlappable instance for small enough primes and testing
instance {-# OVERLAPPABLE #-} (KnownNat p, KnownPrime p) => Prime p where

type family KnownPrime p where
  KnownPrime p = If (IsPrime p) (() :: Constraint) (TypeError (NotPrimeError p))

type NotPrimeError p =
  'Text "Error: " ':<>: 'ShowType p ':<>: 'Text " is not a prime number."

type family IsPrime p where
  IsPrime 0 = 'False
  IsPrime 1 = 'False
  IsPrime 2 = 'True
  IsPrime 3 = 'True
  IsPrime n = NotDivides n 2 (Sqrt n)

type Divides dividend divisor = Mod dividend divisor <=? 0

type family NotDivides dividend divisor0 divisor1 where
  NotDivides dividend divisor divisor = Not (Divides dividend divisor)
  NotDivides dividend divisor0 divisor1 =
    Not (Divides dividend divisor0) && NotDivides dividend (divisor0 + 1) divisor1

type family Sqrt n where
  Sqrt 0 = 0
  Sqrt n = 2 ^ (Log2 n `Div` 2)
