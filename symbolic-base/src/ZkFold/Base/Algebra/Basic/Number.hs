{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.Number
    ( Natural
    , KnownNat
    , KnownInt (..)
    , Prime
    , KnownPrime
    , IsPrime
    , Log2
    , Mod
    , Div
    , Bezout1
    , value
    , type (<=)
    , type (*)
    , type (+)
    , type (-)
    , type (^)
    ) where

import           Data.Kind      (Constraint)
import           Data.Type.Bool (If, type (&&))
import           Data.Type.Ord  (type (<?))
import           GHC.Exts       (proxy#)
import           GHC.TypeLits   (ErrorMessage (..), TypeError)
import           GHC.TypeNats
import           Prelude        (Bool (..), Integer)
import qualified Prelude
import Data.Function (($))

-- Use orphan instances for large publicly verified primes
class KnownNat p => Prime p

value :: forall n . KnownNat n => Natural
value = natVal' (proxy# @n)

class KnownInt (n :: (Bool, Natural)) where
  intValue :: Integer

instance KnownNat n => KnownInt '(False, n) where
  intValue = Prelude.fromIntegral (value @n)

instance KnownNat n => KnownInt '(True, n) where
  intValue = Prelude.negate $ Prelude.fromIntegral (value @n)

-- Use this overlappable instance for small enough primes and testing
instance {-# OVERLAPPABLE #-} (KnownNat p, KnownPrime p) => Prime p

type family KnownPrime p where
  KnownPrime p = If (IsPrime p) (() :: Constraint) (TypeError (NotPrimeError p))

type NotPrimeError p =
  'Text "Error: " ':<>: 'ShowType p ':<>: 'Text " is not a prime number."

type family IsPrime p where
  IsPrime 0 = 'False
  IsPrime 1 = 'False
  IsPrime 2 = 'True
  IsPrime 3 = 'True
  IsPrime n = NotDividesFromTo n 2 (AtLeastSqrt n)

type family NotZero n where
  NotZero 0 = 'False
  NotZero n = 'True

type family NotDividesFromTo dividend divisor0 divisor1 where
  NotDividesFromTo dividend divisor divisor = NotZero (dividend `Mod` divisor)
  NotDividesFromTo dividend divisor0 divisor1 =
    NotZero (dividend `Mod` divisor0) && NotDividesFromTo dividend (divisor0 + 1) divisor1

type family AtLeastSqrt n where
  AtLeastSqrt 0 = 0
  AtLeastSqrt n = 2 ^ (Log2 n `Div` 2 + 1)

type Bezout1 m n = Snd (EGCD m n)

type family Snd t where
  Snd '(_, x) = x

type family EGCD m n where
  EGCD m n = EGCDBody m n False 1 False 0

type family EGCDBody r r' sgn s sgn' s' where
  EGCDBody r 0  sgn   s _     _  = '(r, '(sgn, s))
  EGCDBody r r' False s False s' =
    If (s <? Div r r' * s')
       (EGCDBody r' (r `Mod` r') False s' True  (Div r r' * s' - s))
       (EGCDBody r' (r `Mod` r') False s' False (s - Div r r' * s'))
  EGCDBody r r' True  s True  s' =
    If (Div r r' * s' <? s)
       (EGCDBody r' (r `Mod` r') True s' True  (s - Div r r' * s'))
       (EGCDBody r' (r `Mod` r') True s' False (Div r r' * s' - s))
  EGCDBody r r' sgn   s sgn'  s' =
    EGCDBody r' (r `Mod` r') sgn' s' sgn (s + Div r r' * s')
