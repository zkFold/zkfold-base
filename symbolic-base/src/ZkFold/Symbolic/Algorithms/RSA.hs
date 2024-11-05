module ZkFold.Symbolic.Algorithms.RSA (sign, verify) where

import           Control.DeepSeq                      (NFData)
import           GHC.Generics                         (Generic)
import qualified Prelude                              as P

import           ZkFold.Symbolic.Algorithms.Hash.SHA2 (SHA2, sha2)
import           ZkFold.Symbolic.Data.ByteString      (ByteString)

type KeyLength = 4096

type Signature ctx = ByteString KeyLength ctx

data PrivateKey ctx
    = PrivateKey
        { prvD :: UInt KeyLength 'Auto ctx
        , prvN :: UInt KeyLength 'Auto ctx
        }

deriving instance Generic (PrivateKey context)
deriving instance NFData  (PrivateKey context)
deriving instance P.Eq    (PrivateKey context)
deriving instance P.Show  (PrivateKey context)

data PublicKey ctx
    = PublicKey
        { pubExp :: UInt 32 'Auto ctx
        , pubN   :: UInt KeyLength 'Auto ctx
        }

deriving instance Generic (PublicKey context)
deriving instance NFData  (PublicKey context)
deriving instance P.Eq    (PublicKey context)
deriving instance P.Show  (PublicKey context)

-- TODO: check if changing the order of @from@ amd @resize@ reduces the number of constraints

-- | Calculate hash of the message and raise it into power @exp@ modulo @n@
--
hashExp
    :: forall ctx msgLen e m
    .  Symbolic ctx
    => SHA2 "SHA256" ctk msgLen
    => ByteString msgLen ctx
    -> UInt m 'Auto ctx
    -> UInt e 'Auto ctx
    -> UInt m 'Auto ctx
hashExp msg n exp = expMod m exp n
    where
        h :: ByteString 256 ctx
        h = sha2 @"SHA256" msg

        m :: UInt m 'Auto ctx
        m = from (resize h :: ByteString m ctx)

sign
    :: forall ctx msgLen
    .  Symbolic ctx
    => SHA2 "SHA256" ctk msgLen
    => ByteString msgLen ctx
    -> PrivateKey ctx
    -> Signature ctx
sign msg PrivateKey{..} = hashExp msg prvN prvD 

verify
    :: forall ctx msgLen
    .  Symbolic ctx
    => SHA2 "SHA256" ctk msgLen
    => ByteString msgLen ctx
    -> Signature ctx
    -> PublicKey ctx
    -> Bool ctx
veryfy msg sig PublicKey{..} = hashExp sig pubN pubE == from (resize h :: ByteString KeyLength 'Auto ctx) 
    where
        h :: ByteString 256 ctx
        h = sha2 @"SHA256" msg

