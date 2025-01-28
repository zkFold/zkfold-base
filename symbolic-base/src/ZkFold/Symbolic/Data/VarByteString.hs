{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module ZkFold.Symbolic.Data.VarByteString
    ( VarByteString (..)
    , append
    , (@+)
    , shiftL
    ) where

import           Control.DeepSeq                   (NFData)
import           Data.Aeson                        (FromJSON (..))
import qualified Data.ByteString                   as Bytes
import           Data.Kind                         (Type)
import           Data.Proxy                        (Proxy (..))
import           Data.String                       (IsString (..))
import           GHC.Generics                      (Generic, Par1 (..))
import           GHC.TypeLits                      (KnownSymbol (..), Symbol, symbolVal)
import           Prelude                           (Integer, const, drop, fmap, otherwise, pure, return, take, type (~),
                                                    ($), (.), (<$>), (<), (<>), (==), (>=))
import qualified Prelude                           as Haskell
import           Test.QuickCheck                   (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.HFunctor         (HFunctor (..))
import           ZkFold.Base.Data.Package          (packWith, unpackWith)
import           ZkFold.Base.Data.Utils            (zipWithM)
import qualified ZkFold.Base.Data.Vector           as V
import           ZkFold.Base.Data.Vector           (Vector (..))
import           ZkFold.Prelude                    (replicateA, (!!))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool         (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.ByteString   (ByteString (..), Resize (..), ShiftBits (..), isSet)
import           ZkFold.Symbolic.Data.Class        (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional  (Conditional, bool)
import           ZkFold.Symbolic.Data.Eq           (Eq)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Data.Input        (SymbolicInput, isValid)

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

deriving stock instance (Haskell.Show (c (Vector n)), Haskell.Show (c Par1)) => Haskell.Show (VarByteString n c)
deriving stock instance (Haskell.Eq (c (Vector n)), Haskell.Eq (c Par1)) => Haskell.Eq (VarByteString n c)
deriving anyclass instance (NFData (c (Vector n)), NFData (c Par1)) => NFData (VarByteString n c)
deriving instance (KnownNat n, Symbolic c) => SymbolicData (VarByteString n c)
deriving instance (KnownNat n, Symbolic c) => SymbolicInput (VarByteString n c)
deriving instance (Symbolic c, KnownNat n) => Eq (Bool c) (VarByteString n c)
deriving instance (Symbolic c, KnownNat n) => Conditional (Bool c) (VarByteString n c)

instance
    ( Symbolic c
    , m * 8 ~ n
    , KnownNat m
    ) => IsString (VarByteString n c) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( Symbolic c
    , m * 8 ~ n
    , KnownNat m
    ) => FromConstant Bytes.ByteString (VarByteString n c) where
    fromConstant bytes = VarByteString (fromConstant @Natural . (*8) . Haskell.fromIntegral $ Bytes.length bytes) (fromConstant bytes)

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
    :: forall m n c
    .  Symbolic c
    => KnownNat m
    => KnownNat n
    => KnownNat (m + n)
    => VarByteString m c
    -> VarByteString n c
    -> VarByteString (m + n) c
append (VarByteString l1 bs1) (VarByteString l2 bs2) = VarByteString (l1 + l2) newBs
    where
        ex1, ex2 :: ByteString (m + n) c
        ex1 = resize bs1
        ex2 = resize bs2

        newBs = ex2 || (ex1 `shiftL` l2)

infixr 6 @+
(@+)
    :: forall m n c
    .  Symbolic c
    => KnownNat m
    => KnownNat n
    => KnownNat (m + n)
    => VarByteString m c
    -> VarByteString n c
    -> VarByteString (m + n) c
(@+) = append

shiftL
    :: forall n c
    .  Symbolic c
    => KnownNat n
    => ByteString n c
    -> FieldElement c
    -> ByteString n c
shiftL bs el = Haskell.foldr (\s b -> bool b (b `shiftBitsL` (2^s)) (isSet elBits s)) bs [0 .. nbits]
    where
        elBits = ByteString $ binaryExpansion el

        -- No need to perform more shifts than this. 
        -- The bytestring will be all zeros beyond this iteration.
        nbits = ilog2 $ value @n

        ilog2 :: Natural -> Natural
        ilog2 1 = 0
        ilog2 n = 1 + ilog2 (n `div` 2)
