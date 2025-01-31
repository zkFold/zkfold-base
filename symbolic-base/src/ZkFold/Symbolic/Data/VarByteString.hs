{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.VarByteString
    ( VarByteString (..)
    , fromNatural
    , append
    , (@+)
    , shiftL
    , shiftR
    , wipeUnassigned
    ) where

import           Control.DeepSeq                   (NFData)
import           Data.Aeson                        (FromJSON (..))
import qualified Data.ByteString                   as Bytes
import           Data.Kind                         (Type)
import           Data.Proxy                        (Proxy (..))
import           Data.String                       (IsString (..))
import           GHC.Generics                      (Generic, Par1 (..))
import           GHC.TypeLits                      (KnownSymbol (..), symbolVal)
import           Prelude                           (type (~), ($), (.), (<$>))
import qualified Prelude                           as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector           (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool         (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.ByteString   (ByteString (..), ShiftBits (..), isSet)
import           ZkFold.Symbolic.Data.Class        (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional  (Conditional, bool)
import           ZkFold.Symbolic.Data.Eq           (Eq)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Data.Input        (SymbolicInput)

-- | A ByteString that has length unknown at compile time but guaranteed to not exceed @maxLen@.
-- The unassigned buffer space (i.e. bits past @bsLength@) should be set to zero at all times.
--
-- TODO: Declare all the instances ByteString has for VarByteString
--
data VarByteString (maxLen :: Natural) (context :: (Type -> Type) -> Type) =
    VarByteString
        { bsLength :: FieldElement context
        , bsBuffer :: ByteString maxLen context
        }
    deriving (Generic)

deriving stock instance (Haskell.Show (ctx (Vector n)), Haskell.Show (ctx Par1)) => Haskell.Show (VarByteString n ctx)
deriving stock instance (Haskell.Eq (ctx (Vector n)), Haskell.Eq (ctx Par1)) => Haskell.Eq (VarByteString n ctx)
deriving anyclass instance (NFData (ctx (Vector n)), NFData (ctx Par1)) => NFData (VarByteString n ctx)
deriving instance (KnownNat n, Symbolic ctx) => SymbolicData (VarByteString n ctx)
deriving instance (KnownNat n, Symbolic ctx) => SymbolicInput (VarByteString n ctx)
deriving instance (Symbolic ctx, KnownNat n) => Eq (Bool ctx) (VarByteString n ctx)
deriving instance (Symbolic ctx, KnownNat n) => Conditional (Bool ctx) (VarByteString n ctx)

instance
    ( Symbolic ctx
    , m * 8 ~ n
    , KnownNat m
    ) => IsString (VarByteString n ctx) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( Symbolic ctx
    , m * 8 ~ n
    , KnownNat m
    ) => FromConstant Bytes.ByteString (VarByteString n ctx) where
    fromConstant bytes = VarByteString (fromConstant @Natural . (*8) . Haskell.fromIntegral $ Bytes.length bytes) (fromConstant bytes)

instance (Symbolic ctx, KnownNat n) => FromConstant Natural (VarByteString n ctx) where
    fromConstant 0 = VarByteString zero (fromConstant @Natural 0)
    fromConstant n = VarByteString (fromConstant $ Haskell.min (value @n) (ilog2 n + 1)) (fromConstant n)

fromNatural :: forall n ctx . (Symbolic ctx, KnownNat n) => Natural -> Natural -> VarByteString n ctx
fromNatural n numBits = VarByteString (fromConstant numBits) (fromConstant n)

instance (Symbolic ctx, KnownNat m, m * 8 ~ n) => FromJSON (VarByteString n ctx) where
    parseJSON v = fromString <$> parseJSON v

-- | Construct a VarByteString from a type-level string calculating its length automatically
--
instance
    ( Symbolic ctx
    , KnownSymbol s
    , m ~ Length s
    , m * 8 ~ l
    , KnownNat m
    ) => IsTypeString s (VarByteString l ctx) where
    fromType = fromString $ symbolVal (Proxy @s)

-- | Join two variable-length ByteStrings and move all the unsaaigned space towards lower indices.
-- Let @u@ denote the unassigned space. Then,
-- uu1010 `append` u10010 == uuu101010010
--
append
    :: forall m n ctx
    .  Symbolic ctx
    => KnownNat m
    => KnownNat n
    => KnownNat (m + n)
    => VarByteString m ctx
    -> VarByteString n ctx
    -> VarByteString (m + n) ctx
append (VarByteString l1 bs1) (VarByteString l2 bs2) = VarByteString (l1 + l2) newBs
    where
        ex1, ex2 :: ByteString (m + n) ctx
        ex1 = resize bs1
        ex2 = resize bs2

        newBs = ex2 || (ex1 `shiftL` l2)

infixr 6 @+
(@+)
    :: forall m n ctx
    .  Symbolic ctx
    => KnownNat m
    => KnownNat n
    => KnownNat (m + n)
    => VarByteString m ctx
    -> VarByteString n ctx
    -> VarByteString (m + n) ctx
(@+) = append

shift
    :: forall n ctx
    .  Symbolic ctx
    => KnownNat n
    => (ByteString n ctx -> Natural -> ByteString n ctx)
    -> ByteString n ctx
    -> FieldElement ctx
    -> ByteString n ctx
shift sh bs el = Haskell.foldr (\s b -> bool b (b `sh` (2^s)) (isSet elBits s)) bs [0 .. nbits]
    where
        elBits = ByteString $ binaryExpansion el

        -- No need to perform more shifts than this.
        -- The bytestring will be all zeros beyond this iteration.
        nbits = ilog2 $ value @n

shiftL
    :: forall n ctx
    .  Symbolic ctx
    => KnownNat n
    => ByteString n ctx
    -> FieldElement ctx
    -> ByteString n ctx
shiftL = shift shiftBitsL

shiftR
    :: forall n ctx
    .  Symbolic ctx
    => KnownNat n
    => ByteString n ctx
    -> FieldElement ctx
    -> ByteString n ctx
shiftR = shift shiftBitsR

-- | Set all the unassigned bits to zero
--
wipeUnassigned :: forall n ctx . (Symbolic ctx, KnownNat n) => VarByteString n ctx -> VarByteString n ctx
wipeUnassigned VarByteString{..} = VarByteString bsLength ((`shiftR` unassigned) . (`shiftL` unassigned) $ bsBuffer)
    where
        unassigned :: FieldElement ctx
        unassigned = fromConstant (value @n) - bsLength
