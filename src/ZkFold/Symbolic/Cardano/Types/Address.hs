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

newtype Address context = Address (AddressType context, (PaymentCredential context, StakingCredential context))

deriving instance (Haskell.Eq (ByteString 4 context), Haskell.Eq (ByteString 224 context))
    => Haskell.Eq (Address context)

deriving instance HApplicative context => SymbolicData (Address context)

deriving via (Structural (Address context))
         instance (Symbolic context) => Eq (Bool context) (Address context)

addressType :: Address context -> AddressType context
addressType (Address (t, _)) = t

paymentCredential :: Address context -> PaymentCredential context
paymentCredential (Address (_, (pc, _))) = pc

stakingCredential :: Address context -> StakingCredential context
stakingCredential (Address (_, (_, sc))) = sc
