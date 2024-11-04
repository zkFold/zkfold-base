module ZkFold.Symbolic.Algorithms.RSA (verify) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import qualified Prelude as P

import ZkFold.Symbolic.Algorithms.Hash.SHA2 (sha2, SHA2)
import ZkFold.Symbolic.Data.ByteString (ByteString)

type Signature ctx = ByteString 256 ctx

data PublicKey ctx 
    = PublicKey
        { pubExp :: UInt 32 'Auto ctx
        , pubN :: UInt 4096 'Auto ctx
        }

deriving instance Generic (UInt n r context)
deriving instance NFData (PublicKey context)
deriving instance P.Eq (PublicKey context)
deriving instance P.Show (PublicKey context)

verify 
    :: forall ctx msgLen
    .  Symbolic ctx 
    => SHA2 "SHA256" ctk msgLen
    => ByteString msgLen ctx 
    -> Signature ctx
    -> PublicKey ctx
    -> Bool ctx
veryfy msg sig PublicKey{..} = P.undefined
    where
        h :: ByteString 256 ctx
        h = sha2 @"SHA256" msg

        
