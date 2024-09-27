{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}
module ZkFold.Symbolic.Data.Helpers where

import           Data.Constraint
import           Data.Constraint.Nat
import           Data.Constraint.Unsafe           (unsafeAxiom)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Number


-- type ExtensionBits inputLen = 8 * (128 - Mod inputLen 128)
-- type ExtendedInputByteString inputLen c = ByteString (8 * inputLen + ExtensionBits inputLen) c


with4n6 :: forall n {r}. KnownNat n => (KnownNat (4 * n + 6) => r) -> r
with4n6 f = withDict (timesNat @4 @n) (withDict (plusNat @(4 * n) @6) f)

with8n  :: forall n {r}. KnownNat n => (KnownNat (8 * n) => r) -> r
with8n = withDict (timesNat @8 @n)

withExtensionBits :: forall n {r}. KnownNat n => (KnownNat (8 * (128 - Mod n 128)) => r) -> r
withExtensionBits = withDict (modBound @n @128) $
                        withDict (modNat @n @128) $
                            withDict (minusNat @128 @(Mod n 128)) $
                                withDict (timesNat @8 @(128 - Mod n 128))

withExtendedInputByteString :: forall n {r}. KnownNat n => (KnownNat (8 * n + 8 * (128 - Mod n 128)) => r) -> r
withExtendedInputByteString = withExtensionBits @n $
                                    withDict (timesNat @8 @n) $
                                        withDict (plusNat @(8 * n) @( 8 * (128 - Mod n 128)))

with8nLessExt :: forall n {r}. KnownNat n => (8 * n <= 8 * n +  8 * (128 - Mod n 128) => r) -> r
with8nLessExt = withExtendedInputByteString @n $
                    withDict (zeroLe @( 8 * (128 - Mod n 128))) $
                        withDict (plusMonotone2 @(8 * n) @0 @( 8 * (128 - Mod n 128)))

---
black2bDivConstraint :: forall a b. (Gcd a 8 ~ 8) :- (Div (8 * a + 8 * (2 * 64 - Mod a (2 * b))) 64 * 64 ~ 8 * a + 8 * (2 * 64 - Mod a (2 * 64)) )
black2bDivConstraint = Sub unsafeAxiom

withBlack2bDivConstraint :: forall a b {r}. (Gcd a 8 ~ 8) => (Div (8 * a + 8 * (2 * 64 - Mod a (2 * b))) 64 * 64 ~ 8 * a + 8 * (2 * 64 - Mod a (2 * 64)) => r) -> r
withBlack2bDivConstraint =  withDict (black2bDivConstraint @a @b)

---
unsafeDiv :: forall a b. Dict (Div a b * b ~ a)
unsafeDiv = unsafeAxiom

withUnsafeDiv :: forall a b {r}. ( (Div a b * b ~ a) => r) -> r
withUnsafeDiv = withDict (unsafeDiv @a @b)

---
gcdn8 :: forall a. Dict (Gcd a 8 ~ 8)
gcdn8 = unsafeAxiom

withGcdn8 :: forall a {r}. ( (Gcd a 8 ~ 8) => r) -> r
withGcdn8 = withDict (gcdn8 @a)

---
with2n :: forall n {r}. KnownNat n => (KnownNat (2 * n) => r) -> r
with2n = withDict (timesNat @2 @n)
