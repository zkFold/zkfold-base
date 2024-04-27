{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.Number (KnownNat, Prime, KnownPrime, IsPrime, value, type (*), type (+), type (-), type (^)) where


import           Data.Kind      (Constraint)
import           Data.Type.Bool (If, type (&&))
import           GHC.Exts       (proxy#)
import           GHC.TypeLits   (ErrorMessage (..), TypeError)
import           GHC.TypeNats
import           Prelude        (Bool (..))

value :: forall n . KnownNat n => Natural
value = natVal' (proxy# @n)

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

type family NotZero n where
  NotZero 0 = 'False
  NotZero n = 'True

type family NotDivides dividend divisor0 divisor1 where
  NotDivides dividend divisor divisor = NotZero (Mod dividend divisor)
  NotDivides dividend divisor0 divisor1 =
    NotZero (Mod dividend divisor0) && NotDivides dividend (divisor0 + 1) divisor1

type family Sqrt n where
  Sqrt 0 = 0
  Sqrt n = 2 ^ (Log2 n `Div` 2)
