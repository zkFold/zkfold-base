{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Address where

import           GHC.Generics                        (Generic)
import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Class               (Symbolic)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional    (Conditional)
import           ZkFold.Symbolic.Data.Eq             (Eq)
import           ZkFold.Symbolic.Data.Input

type AddressType context = ByteString 4 context
type PaymentCredential context = ByteString 224 context
type StakingCredential context = ByteString 224 context

data Address context = Address {
        addressType       :: AddressType context,
        paymentCredential :: PaymentCredential context,
        stakingCredential :: StakingCredential context
    }
    deriving (Generic)

deriving instance (Haskell.Eq (ByteString 4 context), Haskell.Eq (ByteString 224 context))
    => Haskell.Eq (Address context)

instance Symbolic context => Eq (Address context)
instance Symbolic context => Conditional (Bool context) (Address context)
instance Symbolic context => SymbolicData (Address context)
instance Symbolic context => SymbolicInput (Address context) where
    isValid (Address a p s) = isValid (a, p, s)
