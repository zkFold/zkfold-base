{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Address where

import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Base.Control.HApplicative    (HApplicative)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Class               (Symbolic)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Eq             (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural

type AddressType context = ByteString 4 context
type PaymentCredential context = ByteString 224 context
type StakingCredential context = ByteString 224 context

data  Address context = Address {
        addressType       :: AddressType context,
        paymentCredential :: PaymentCredential context,
        stakingCredential :: StakingCredential context
    }

deriving instance (Haskell.Eq (ByteString 4 context), Haskell.Eq (ByteString 224 context))
    => Haskell.Eq (Address context)


deriving via (Structural (Address context))
         instance (Symbolic context) => Eq (Bool context) (Address context)

instance HApplicative context => SymbolicData (Address context) where
  type Context (Address context) = Context (AddressType context, PaymentCredential context, StakingCredential context)
  type Support (Address context) = Support (AddressType context, PaymentCredential context, StakingCredential context)
  type Layout (Address context) = Layout (AddressType context, PaymentCredential context, StakingCredential context)
  pieces (Address a b c) = pieces (a, b, c)
  restore f = let (a, b, c) = restore f in Address a b c
