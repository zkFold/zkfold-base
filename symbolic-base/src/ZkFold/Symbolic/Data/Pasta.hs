{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Data.Pasta where

import           GHC.Generics                            (Generic)
import           Prelude                                 (fromInteger, type (~), ($))
import qualified Prelude                                 as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Pasta (FqModulus)
import           ZkFold.Base.Data.Vector                 (Vector)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class              (Context)
import           ZkFold.Symbolic.Data.Combinators        (RegisterSize (..))
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq                 (SymbolicEq, Eq (BooleanOf), (==))
import           ZkFold.Symbolic.Data.FFA                (FFA, KnownFFA)

------------------------------ Weierstrass instances ------------------------------

instance Field field => WeierstrassCurve "Pasta-Sym" field where
  weierstrassB = fromConstant (5 :: Natural)

instance
  ( Finite field
  , WeierstrassCurve "Pasta-Sym" field
  , KnownFFA FqModulus (Fixed 1) (Context field)
  , SymbolicEq field
  ) => CyclicGroup (Weierstrass "Pasta-Sym" (Point field)) where
    type ScalarFieldOf (Weierstrass "Pasta-Sym" (Point field)) = FFA FqModulus (Fixed 1) (Context field)
    pointGen = pointXY
      (fromConstant (value @(Order field) -! 1))
      (fromConstant (0x02 :: Natural))

instance
  ( WeierstrassCurve "Pasta-Sym" field
  , KnownFFA FqModulus (Fixed 1) (Context field)
  , SymbolicEq field
  , Context field ~ ctx
  ) => Scale (FFA FqModulus (Fixed 1) ctx) (Weierstrass "Pasta-Sym" (Point field)) where

    scale sc x = sum $ P.zipWith (\b p -> bool @(Bool ctx) zero p (isSet bits b)) [upper, upper -! 1 .. 0] (P.iterate (\e -> e + e) x)
        where
            bits :: ByteString 255 ctx
            bits = binaryExpansion sc

            upper :: Natural
            upper = 255 -! 1

--------------------------------- Pasta point ---------------------------------

data PallasPoint field = PallasPoint field field field
  deriving (Generic, P.Functor, P.Foldable, P.Traversable, P.Show)

toWeierstrass :: (Field field, Eq field)
  => PallasPoint field -> Weierstrass "Pasta-Sym" (Point field)
toWeierstrass (PallasPoint x y z) = Weierstrass (Point x y (z == one))

fromWeierstrass :: (Field field, Eq field)
  => Weierstrass "Pasta-Sym" (Point field) -> PallasPoint field
fromWeierstrass (Weierstrass (Point x y z)) = PallasPoint x y (bool zero one z)

instance (Eq (PallasPoint field), P.Eq (BooleanOf field)) => P.Eq (PallasPoint field) where
  p1 == p2 = (p1 == p2) P.== true

instance (Field field, SymbolicEq field, Context field ~ ctx) => Conditional (Bool ctx) (PallasPoint field)
instance (Field field, SymbolicEq field) => Eq (PallasPoint field) where
  PallasPoint x1 y1 z1 == PallasPoint x2 y2 z2 = x1 == x2 && y1 == y2 && z1 == z2
instance (WeierstrassCurve "Pasta-Sym" field, SymbolicEq field)
  => AdditiveSemigroup (PallasPoint field) where
    p1 + p2 = fromWeierstrass $ toWeierstrass p1 + toWeierstrass p2
instance (WeierstrassCurve "Pasta-Sym" field, SymbolicEq field)
  => Scale Natural (PallasPoint field) where
    scale sc p = fromWeierstrass $ scale sc $ toWeierstrass p
instance (WeierstrassCurve "Pasta-Sym" field, SymbolicEq field)
  => AdditiveMonoid (PallasPoint field) where
    zero = fromWeierstrass zero
instance (WeierstrassCurve "Pasta-Sym" field, SymbolicEq field)
  => Scale P.Integer (PallasPoint field) where
    scale sc p = fromWeierstrass $ scale sc $ toWeierstrass p
instance (WeierstrassCurve "Pasta-Sym" field, SymbolicEq field)
  => AdditiveGroup (PallasPoint field) where
    negate p = fromWeierstrass $ negate $ toWeierstrass p
instance
  ( Finite field
  , WeierstrassCurve "Pasta-Sym" field
  , KnownFFA FqModulus (Fixed 1) (Context field)
  , SymbolicEq field
  ) => CyclicGroup (PallasPoint field) where
    type ScalarFieldOf (PallasPoint field) = FFA FqModulus (Fixed 1) (Context field)
    pointGen = fromWeierstrass pointGen
instance
  ( WeierstrassCurve "Pasta-Sym" field
  , KnownFFA FqModulus (Fixed 1) (Context field)
  , SymbolicEq field
  , ctx ~ Context field
  ) => Scale (FFA FqModulus (Fixed 1) ctx) (PallasPoint field) where
    scale sc p = fromWeierstrass $ scale sc $ toWeierstrass p

instance {-# INCOHERENT #-}
  ( WeierstrassCurve "Pasta-Sym" field
  , KnownFFA FqModulus (Fixed 1) (Context field)
  , SymbolicEq field
  , BinaryExpansion field
  , Bits field ~ ctx (Vector (NumberOfBits field))
  , Log2 (Order field - 1) ~ 254
  , ctx ~ Context field
  ) => Scale field (PallasPoint field) where
    scale x = scale (fromBinary @(FFA FqModulus (Fixed 1) ctx) $ ByteString $ binaryExpansion x)
