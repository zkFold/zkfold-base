{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Data.Pasta (PallasPoint) where

import           Prelude                                 (fromInteger, type (~), ($))
import qualified Prelude                                 as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.Vector                 (Vector)
import           ZkFold.Symbolic.Class                   (Symbolic (..))
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class              (Context)
import           ZkFold.Symbolic.Data.Combinators        (KnownRegisterSize, RegisterSize (..))
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq                 (Eq (..), SymbolicEq)
import           ZkFold.Symbolic.Data.UInt               (UInt (..))

--------------------------------- UInt instances ---------------------------------

instance (KnownNat (2^n), KnownNat (Log2 (2^n-1)+1)) => Finite (UInt n r ctx) where
  type Order (UInt n r ctx) = 2^n

instance (KnownNat n, KnownRegisterSize r, Symbolic ctx) => Exponent (UInt n r ctx) P.Integer where
    (^) = intPow

-- TODO: optimize this
instance (KnownNat n, KnownRegisterSize r, Symbolic ctx) => MultiplicativeGroup (UInt n r ctx) where
  invert x = natPow x (2 P.^ (value @n) -! 2)

instance (KnownNat n, KnownRegisterSize r, Symbolic ctx) => Field (UInt n r ctx) where
  finv = invert

instance (KnownNat n, Symbolic ctx) => BinaryExpansion (UInt n (Fixed 1) ctx) where
  type Bits (UInt n (Fixed 1) ctx) = ctx (Vector n)
  binaryExpansion (UInt x) = x
  fromBinary = UInt

------------------------------ Weierstrass instances ------------------------------

-- TODO: use the actual scalar field
instance
  ( Finite field
  , WeierstrassCurve "Pasta" field
  , SymbolicEq field
  ) => CyclicGroup (Weierstrass "Pasta" (Point field)) where
    type ScalarFieldOf (Weierstrass "Pasta" (Point field)) = UInt 255 (Fixed 1) (Context field)
    pointGen = pointXY
      (fromConstant (value @(Order field) -! 1))
      (fromConstant (0x02 :: Natural))

instance
  ( WeierstrassCurve "Pasta" field
  , SymbolicEq field
  , Context field ~ ctx
  ) => Scale (UInt 255 (Fixed 1) ctx) (Weierstrass "Pasta" (Point field)) where

    scale sc x = sum $ P.zipWith (\b p -> bool @(Bool ctx) zero p (isSet bits b)) [upper, upper -! 1 .. 0] (P.iterate (\e -> e + e) x)
        where
            bits :: ByteString 255 ctx
            bits = ByteString $ binaryExpansion sc

            upper :: Natural
            upper = 255 -! 1

--------------------------------- Pasta point ---------------------------------

data PallasPoint field = PallasPoint field field field
  deriving (P.Functor)

toWeierstrass :: (Field field, Eq field)
  => PallasPoint field -> Weierstrass "Pasta" (Point field)
toWeierstrass (PallasPoint x y z) = Weierstrass (Point x y (z == one))

fromWeierstrass :: (Field field, Eq field)
  => Weierstrass "Pasta" (Point field) -> PallasPoint field
fromWeierstrass (Weierstrass (Point x y z)) = PallasPoint x y (bool zero one z)

instance (WeierstrassCurve "Pasta" field, SymbolicEq field)
  => AdditiveSemigroup (PallasPoint field) where
    p1 + p2 = fromWeierstrass $ toWeierstrass p1 + toWeierstrass p2
instance (WeierstrassCurve "Pasta" field, SymbolicEq field)
  => Scale Natural (PallasPoint field) where
    scale sc p = fromWeierstrass $ scale sc $ toWeierstrass p
instance (WeierstrassCurve "Pasta" field, SymbolicEq field)
  => AdditiveMonoid (PallasPoint field) where
    zero = fromWeierstrass zero
instance (WeierstrassCurve "Pasta" field, SymbolicEq field)
  => Scale P.Integer (PallasPoint field) where
    scale sc p = fromWeierstrass $ scale sc $ toWeierstrass p
instance (WeierstrassCurve "Pasta" field, SymbolicEq field)
  => AdditiveGroup (PallasPoint field) where
    negate p = fromWeierstrass $ negate $ toWeierstrass p
instance
  ( Finite field
  , WeierstrassCurve "Pasta" field
  , SymbolicEq field
  ) => CyclicGroup (PallasPoint field) where
    type ScalarFieldOf (PallasPoint field) = UInt 255 (Fixed 1) (Context field)
    pointGen = fromWeierstrass pointGen
instance
  ( WeierstrassCurve "Pasta" field
  , SymbolicEq field
  , ctx ~ Context field
  ) => Scale (UInt 255 (Fixed 1) ctx) (PallasPoint field) where
    scale sc p = fromWeierstrass $ scale sc $ toWeierstrass p
