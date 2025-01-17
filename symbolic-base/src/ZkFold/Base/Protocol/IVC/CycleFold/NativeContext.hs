{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}

module ZkFold.Base.Protocol.IVC.CycleFold.NativeContext where

import           GHC.Generics                                      ((:.:) (..))
import           Prelude                                           (type (~), fmap, ($), undefined)

import           ZkFold.Base.Algebra.Basic.Class                   (Scale, FromConstant (..), zero, MultiplicativeMonoid (..))
import           ZkFold.Base.Algebra.Basic.Number                  (KnownNat, type (+), type (-))
import           ZkFold.Base.Data.ByteString                       (Binary)
import           ZkFold.Base.Data.Package                          (packed)
import           ZkFold.Base.Data.Vector                           (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme        (AccumulatorScheme (..))
import           ZkFold.Base.Protocol.IVC.CycleFold.ForeignContext
import ZkFold.Base.Protocol.IVC.CycleFold.Utils                    (PrimaryGroup, ForeignField, SecondaryGroup)
import           ZkFold.Base.Protocol.IVC.FiatShamir               (FiatShamir)
import           ZkFold.Base.Protocol.IVC.NARK                     (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Symbolic.Class                             (Symbolic(..))
import           ZkFold.Symbolic.Data.FieldElement                 (FieldElement (..))

type ForeignOperationInput = NativeOperationInput :.: ForeignField

type ForeignOperation = NativeOperation :.: ForeignField

type ForeignPayload = NativePayload :.: ForeignField

--------------------------------------------------------------------------------

data ForeignPoint k ctx = ForeignPoint
    { fpValue               :: ForeignOperation (FieldElement ctx)
    , fpAccumulatorInstance :: (AccumulatorInstance k NativeOperation SecondaryGroup :.: ForeignField) (FieldElement ctx)
    , fpAccumulatorProof    :: (Vector k :.: [] :.: ForeignField) (WitnessField ctx)
    }

--------------------------------------------------------------------------------

toNative :: forall t ctx . (t :.: ForeignField) (WitnessField ctx) -> t (WitnessField (ForeignContext ctx))
toNative = undefined

fromNative :: t (WitnessField (ForeignContext ctx)) -> (t :.: ForeignField) (WitnessField ctx)
fromNative = undefined

--------------------------------------------------------------------------------

fopCircuit :: forall algo d k ctx .
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    )
    => ForeignPoint k ctx
    -> ForeignOperationInput (WitnessField ctx)
    -> ForeignPoint k ctx
fopCircuit ForeignPoint {..} opF =
    let
        gF :: (PrimaryGroup :.: ForeignField) (WitnessField ctx)
        gF = witnessF $ packed $ fmap fromFieldElement $ Comp1 $ opRes $ unComp1 fpValue

        gN :: PrimaryGroup (WitnessField (ForeignContext ctx))
        gN = toNative @_ @ctx gF

        opN :: NativeOperationInput (WitnessField (ForeignContext ctx))
        opN = toNative @_ @ctx opF

        protocol :: FiatShamir k NativeOperation NativePayload PrimaryGroup (ForeignContext ctx)
        protocol = opProtocol @algo @d

        input0 :: NativeOperation (WitnessField (ForeignContext ctx))
        input0 = NativeOperation zero zero zero zero zero

        payload :: NativePayload (WitnessField (ForeignContext ctx))
        payload = case opN of
            Addition h       -> NativePayload zero gN h    zero
            Multiplication s -> NativePayload s    gN zero one

        narkIP :: NARKInstanceProof k NativeOperation PrimaryGroup (ForeignContext ctx)
        narkIP@(NARKInstanceProof input (NARKProof pi_x pi_w)) = narkInstanceProof protocol input0 payload

        scheme :: AccumulatorScheme d k NativeOperation PrimaryGroup (ForeignContext ctx)
        scheme = opAccumulatorScheme @algo

        accX :: AccumulatorInstance k NativeOperation SecondaryGroup (WitnessField (ForeignContext ctx))
        accX = undefined

        accW :: Vector k [WitnessField (ForeignContext ctx)]
        accW = undefined

        acc :: Accumulator k NativeOperation SecondaryGroup (WitnessField (ForeignContext ctx))
        acc = Accumulator accX accW

        (acc', pf) = prover scheme acc narkIP

        -- The result of the accumulation verifier
        accX' = undefined

        -- The accumulator witness obtained from `acc'`
        accW' = undefined

        inputF :: ForeignOperation (FieldElement ctx)
        inputF = undefined

    in ForeignPoint inputF accX' accW'
