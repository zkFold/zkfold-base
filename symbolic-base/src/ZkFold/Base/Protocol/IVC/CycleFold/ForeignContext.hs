{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}

module ZkFold.Base.Protocol.IVC.CycleFold.ForeignContext where

import           Data.Distributive (Distributive (..))
import           Data.Functor.Rep                           (Representable (..), distributeRep, collectRep, mzipWithRep)
import           Data.These                                 (These(..))
import           Data.Zip                                   (Zip (..), Semialign (..))
import           GHC.Generics                               (Par1 (..), Generic, Generic1)
import           Prelude                                    (Functor, Traversable, type (~), fmap, ($), Foldable)

import           ZkFold.Base.Algebra.Basic.Class            (Scale (..), FromConstant (..), AdditiveSemigroup (..))
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (+), type (-))
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Data.Package                   (unpacked)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.CommitOpen        (commitOpen)
import           ZkFold.Base.Protocol.IVC.CycleFold.Utils   (PrimaryField, PrimaryGroup, SecondaryGroup)
import           ZkFold.Base.Protocol.IVC.FiatShamir        (FiatShamir, fiatShamir)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.SpecialSound      (specialSoundProtocol)
import           ZkFold.Symbolic.Class                      (Symbolic(..), embedW)
import           ZkFold.Symbolic.Data.Bool                  (Bool (..))
import           ZkFold.Symbolic.Data.Conditional           (Conditional (..))
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (..))
import           ZkFold.Symbolic.Data.Payloaded             (Payloaded (..))

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

instance Distributive NativeOperation where
    distribute = distributeRep
    collect = collectRep

instance Representable NativeOperation

instance Semialign NativeOperation where
    alignWith f = mzipWithRep (\a b -> f (These a b))

instance Zip NativeOperation where
    zipWith = mzipWithRep

--------------------------------------------------------------------------------

data NativePayload f = NativePayload (PrimaryField f) (PrimaryGroup f) (PrimaryGroup f) (Par1 f)
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance Distributive NativePayload where
    distribute = distributeRep
    collect = collectRep

instance Representable NativePayload

--------------------------------------------------------------------------------

opCircuit :: forall ctx . Symbolic ctx
    => NativeOperation (FieldElement ctx)
    -> Payloaded NativePayload ctx
    -> NativeOperation (FieldElement ctx)
opCircuit _ (Payloaded (NativePayload s g h op)) =
    let
        opS :: PrimaryField (FieldElement ctx)
        opS = fmap FieldElement $ unpacked $ embedW s

        opG :: PrimaryGroup (FieldElement ctx)
        opG = fmap FieldElement $ unpacked $ embedW g

        opH :: PrimaryGroup (FieldElement ctx)
        opH = fmap FieldElement $ unpacked $ embedW h

        opId :: FieldElement ctx
        opId = unPar1 $ fmap FieldElement $ unpacked $ embedW op

        opRes :: PrimaryGroup (FieldElement ctx)
        opRes = bool (opG + opH) (scale opS opG) $ Bool $ fromFieldElement opId
    in NativeOperation {..}

opPredicate :: forall ctx .
    ( Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    )
    => Predicate NativeOperation NativePayload (ForeignContext ctx)
opPredicate = predicate opCircuit

opProtocol :: forall algo d k ctx .
    ( HashAlgorithm algo
    , KnownNat (d + 1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    )
    => FiatShamir k NativeOperation NativePayload SecondaryGroup (ForeignContext ctx)
opProtocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d opPredicate

opAccumulatorScheme :: forall algo d k ctx .
    ( HashAlgorithm algo
    , KnownNat (d - 1)
    , KnownNat (d + 1)
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    )
    => AccumulatorScheme d k NativeOperation SecondaryGroup (ForeignContext ctx)
opAccumulatorScheme = accumulatorScheme @algo opPredicate
