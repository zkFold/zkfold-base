{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Algorithms.RSA
    ( sign
    , verify
    , RSA
    , PublicKey (..)
    , PrivateKey (..)
    , Signature
    , KeyLength
    ) where

import           Control.DeepSeq                      (NFData, force)
import           GHC.Generics                         (Generic)
import           Prelude                              (($))
import qualified Prelude                              as P

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector              (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.SHA2 (SHA2, sha2)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool            (Bool, (&&))
import           ZkFold.Symbolic.Data.ByteString      (ByteString)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators     (Ceil, GetRegisterSize, Iso (..), NumberOfRegisters,
                                                       RegisterSize (..), Resize (..))
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Input           (SymbolicInput, isValid)
import           ZkFold.Symbolic.Data.UInt            (OrdWord, UInt, expMod)

type KeyLength = 512

type Signature ctx = ByteString KeyLength ctx

data PrivateKey ctx
    = PrivateKey
        { prvD :: UInt KeyLength 'Auto ctx
        , prvN :: UInt KeyLength 'Auto ctx
        }

deriving instance Generic (PrivateKey context)
deriving instance (NFData (context (Vector (NumberOfRegisters (BaseField context) KeyLength 'Auto)))) => NFData (PrivateKey context)
deriving instance (P.Eq (context (Vector (NumberOfRegisters (BaseField context) KeyLength 'Auto))))   => P.Eq   (PrivateKey context)
deriving instance
    ( P.Show (BaseField context)
    , P.Show (context (Vector (NumberOfRegisters (BaseField context) KeyLength 'Auto)))
    ) => P.Show (PrivateKey context)

deriving instance Symbolic ctx => SymbolicData (PrivateKey ctx)

instance
  ( Symbolic ctx
  , KnownNat (NumberOfRegisters (BaseField ctx) KeyLength 'Auto)
  ) => SymbolicInput (PrivateKey ctx) where
    isValid PrivateKey{..} = isValid prvD && isValid prvN

data PublicKey ctx
    = PublicKey
        { pubE :: UInt 32 'Auto ctx
        , pubN :: UInt KeyLength 'Auto ctx
        }

deriving instance Generic (PublicKey context)
deriving instance
    ( NFData (context (Vector (NumberOfRegisters (BaseField context) KeyLength 'Auto)))
    , NFData (context (Vector (NumberOfRegisters (BaseField context) 32 'Auto)))
    ) =>  NFData  (PublicKey context)
deriving instance
    ( P.Eq (context (Vector (NumberOfRegisters (BaseField context) KeyLength 'Auto)))
    , P.Eq (context (Vector (NumberOfRegisters (BaseField context) 32 'Auto)))
    ) =>  P.Eq    (PublicKey context)
deriving instance
    ( P.Show (context (Vector (NumberOfRegisters (BaseField context) KeyLength 'Auto)))
    , P.Show (context (Vector (NumberOfRegisters (BaseField context) 32 'Auto)))
    , P.Show (BaseField context)
    ) =>  P.Show  (PublicKey context)

deriving instance Symbolic ctx => SymbolicData (PublicKey ctx)

instance
  ( Symbolic ctx
  , KnownNat (NumberOfRegisters (BaseField ctx) KeyLength 'Auto)
  , KnownNat (NumberOfRegisters (BaseField ctx) 32 'Auto)
  ) => SymbolicInput (PublicKey ctx) where
    isValid PublicKey{..} = isValid pubE && isValid pubN

type RSA ctx msgLen =
   ( SHA2 "SHA256" ctx msgLen
   , KnownNat (NumberOfRegisters (BaseField ctx) KeyLength 'Auto)
   , KnownNat (NumberOfRegisters (BaseField ctx) (2 * KeyLength) 'Auto)
   , KnownNat (Ceil (GetRegisterSize (BaseField ctx) (2 * KeyLength) 'Auto) OrdWord)
   , NFData (ctx (Vector KeyLength))
   , NFData (ctx (Vector (NumberOfRegisters (BaseField ctx) KeyLength 'Auto)))
   , NFData (ctx (Vector (NumberOfRegisters (BaseField ctx) (2 * KeyLength) 'Auto)))
   )

sign
    :: forall ctx msgLen
    .  RSA ctx msgLen
    => ByteString msgLen ctx
    -> PrivateKey ctx
    -> Signature ctx
sign msg PrivateKey{..} = force $ from $ expMod msgI prvD prvN
    where
        h :: ByteString 256 ctx
        h = sha2 @"SHA256" msg

        msgI :: UInt 256 'Auto ctx
        msgI = from h

verify
    :: forall ctx msgLen
    .  RSA ctx msgLen
    => ByteString msgLen ctx
    -> Signature ctx
    -> PublicKey ctx
    -> Bool ctx
verify msg sig PublicKey{..} = target == input
    where
        h :: ByteString 256 ctx
        h = sha2 @"SHA256" msg

        target :: UInt KeyLength 'Auto ctx
        target = force $ expMod (from sig :: UInt KeyLength 'Auto ctx) pubE pubN

        input :: UInt KeyLength 'Auto ctx
        input = force $ resize (from h :: UInt 256 'Auto ctx)
