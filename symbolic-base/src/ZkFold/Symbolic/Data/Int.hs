{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE NoDeriveAnyClass     #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Int where

import ZkFold.Symbolic.Data.UInt
import ZkFold.Base.Algebra.Basic.Number (Natural, KnownNat)
import ZkFold.Symbolic.Data.Combinators (RegisterSize, KnownRegisterSize)
import Data.Kind (Type)
import ZkFold.Base.Algebra.Basic.Class (Ring, AdditiveGroup, AdditiveMonoid, AdditiveSemigroup, Scale, FromConstant, Semiring, MultiplicativeMonoid, Exponent (..), MultiplicativeSemigroup)
import ZkFold.Symbolic.Class (Symbolic)
import qualified GHC.Num.Integer

newtype Int (n :: Natural) (r :: RegisterSize) (context :: (Type -> Type) -> Type) = Int (UInt n r context)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => AdditiveSemigroup (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Scale Natural (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => AdditiveMonoid (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Scale GHC.Num.Integer.Integer (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => AdditiveGroup (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => FromConstant GHC.Num.Integer.Integer (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => FromConstant Natural (Int n r c)

instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Exponent (Int n r c) Natural
  where
    Int u ^ p = Int (u ^ p)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => MultiplicativeSemigroup (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => MultiplicativeMonoid (Int n r c)

deriving instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Semiring (Int n r c)

instance
    ( Symbolic c
    , KnownNat n
    , KnownRegisterSize r
    ) => Ring (Int n r c)
