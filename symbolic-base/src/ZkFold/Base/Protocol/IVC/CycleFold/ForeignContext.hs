{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.CycleFold.ForeignContext where

import           Control.DeepSeq                            (NFData1)
import           Data.Distributive                          (Distributive (..))
import           Data.Functor.Rep                           (Representable (..), collectRep, distributeRep, mzipWithRep)
import           Data.These                                 (These (..))
import           Data.Zip                                   (Semialign (..), Zip (..))
import           GHC.Generics                               (Generic, Generic1, Par1 (..))
import           Prelude                                    (Foldable, Functor, Traversable, return, type (~), ($))
import qualified Prelude                                    as Haskell
import           Test.QuickCheck                            (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class            (AdditiveSemigroup (..), FiniteField, Scale (..), one, zero,
                                                             (*), (+), (-))
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (+), type (-))
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.CommitOpen        (commitOpen)
import           ZkFold.Base.Protocol.IVC.CycleFold.Utils   (PrimaryField, PrimaryGroup, SecondaryGroup)
import           ZkFold.Base.Protocol.IVC.FiatShamir        (FiatShamir, fiatShamir)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.SpecialSound      (specialSoundProtocol)
import           ZkFold.Symbolic.Class                      (Arithmetic)

type ForeignContext ctx = ctx

--------------------------------------------------------------------------------

data NativeOperationInput f =
      Addition (PrimaryGroup f)
    | Multiplication (PrimaryField f)
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

--------------------------------------------------------------------------------

data NativeOperation f = NativeOperation
    { opS   :: PrimaryField f
    , opG   :: PrimaryGroup f
    , opH   :: PrimaryGroup f
    , opRes :: PrimaryGroup f
    , opId  :: f
    }
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance Haskell.Eq (PrimaryGroup f) => Haskell.Eq (NativeOperation f) where
    op1 == op2 = opRes op1 Haskell.== opRes op2

opInit :: FiniteField f => f -> NativeOperation f
opInit s = NativeOperation
    { opS   = zero
    , opG   = zero
    , opH   = zero
    , opRes = Par1 s
    , opId  = zero
    }

instance Distributive NativeOperation where
    distribute = distributeRep
    collect = collectRep

instance Representable NativeOperation

instance Semialign NativeOperation where
    alignWith f = mzipWithRep (\a b -> f (These a b))

instance Zip NativeOperation where
    zipWith = mzipWithRep

instance Binary a => Binary (NativeOperation a)

instance NFData1 NativeOperation

instance
    ( FiniteField f
    , Arbitrary (PrimaryField f)
    ) => Arbitrary (NativeOperation f) where
    arbitrary = do
        s <- arbitrary
        g <- arbitrary
        h <- arbitrary
        op <- arbitrary
        return $ if op
            then NativeOperation s g h (g + h) zero
            else NativeOperation s g h (scale s g) one

--------------------------------------------------------------------------------

data NativePayload f = NativePayload (PrimaryField f) (PrimaryGroup f) (PrimaryGroup f) (Par1 f)
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance Distributive NativePayload where
    distribute = distributeRep
    collect = collectRep

instance Representable NativePayload

instance Binary a => Binary (NativePayload a)

instance NFData1 NativePayload

instance
    ( FiniteField f
    , Arbitrary (PrimaryField f)
    ) => Arbitrary (NativePayload f) where
    arbitrary = do
        s <- arbitrary
        g <- arbitrary
        h <- arbitrary
        op <- arbitrary
        return $ NativePayload s g h (if op then zero else one)

--------------------------------------------------------------------------------

opCircuit :: forall f . FiniteField f
    => NativeOperation f
    -> NativePayload f
    -> NativeOperation f
opCircuit _ ((NativePayload s g h op)) =
    let
        opS :: PrimaryField f
        opS = s

        opG :: PrimaryGroup f
        opG = g

        opH :: PrimaryGroup f
        opH = h

        opId :: f
        opId = unPar1 op

        opRes :: PrimaryGroup f
        opRes = mzipWithRep (\v1 v2 -> v1 + (v2-v1)*opId) (opG + opH) (scale opS opG)
    in NativeOperation {..}

opPredicate :: forall a .
    ( Arithmetic a
    , Binary a
    )
    => Predicate a NativeOperation NativePayload
opPredicate = predicate opCircuit

opProtocol :: forall algo d k a .
    ( HashAlgorithm algo
    , KnownNat (d + 1)
    , k ~ 1
    , Arithmetic a
    , Binary a
    )
    => FiatShamir k a NativeOperation NativePayload SecondaryGroup
opProtocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d $ opPredicate

opAccumulatorScheme :: forall algo d k a .
    ( HashAlgorithm algo
    , KnownNat (d - 1)
    , KnownNat (d + 1)
    , Arithmetic a
    , Binary a
    )
    => AccumulatorScheme d k a NativeOperation SecondaryGroup
opAccumulatorScheme = accumulatorScheme @algo $ opPredicate
