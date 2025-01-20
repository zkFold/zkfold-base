{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.CycleFold.NativeContext where

import           Control.Lens                                      ((^.))
import           GHC.Generics                                      ((:.:) (..), Par1 (..))
import           Prelude                                           (Integer, Functor (..), Foldable, Traversable, type (~), undefined, const, return, (.), ($), (<$>))
import qualified Prelude                                           as Haskell
import           Test.QuickCheck                                   (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                   (Zp)
import           ZkFold.Base.Algebra.Basic.Number                  (KnownNat, type (+), type (-), Natural)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381       (BLS12_381_Scalar)
import           ZkFold.Base.Data.ByteString                       (Binary)
import           ZkFold.Base.Data.Package                          (packed, unpacked)
import           ZkFold.Base.Data.Vector                           (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme        (AccumulatorScheme (..))
import           ZkFold.Base.Protocol.IVC.CycleFold.ForeignContext
import ZkFold.Base.Protocol.IVC.CycleFold.Utils                    (PrimaryGroup, ForeignField, SecondaryGroup, PrimaryField)
import           ZkFold.Base.Protocol.IVC.NARK                     (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Symbolic.Data.Bool                         (Bool)
import           ZkFold.Symbolic.Class                             (Symbolic(..), embedW)
import           ZkFold.Symbolic.Data.FieldElement                 (FieldElement (..))

type ForeignOperationInput = NativeOperationInput :.: ForeignField

type ForeignOperation = NativeOperation :.: ForeignField

type ForeignPayload = NativePayload :.: ForeignField

--------------------------------------------------------------------------------

data ForeignPoint algo (d :: Natural) k ctx = ForeignPoint
    { fpValue               :: ForeignOperation (FieldElement ctx)
    , fpAccumulatorInstance :: (AccumulatorInstance k NativeOperation SecondaryGroup :.: ForeignField) (FieldElement ctx)
    , fpAccumulatorProof    :: ((Vector k :.: []) :.: ForeignField) (WitnessField ctx)
    }

fpIsValid :: ForeignPoint algo d k ctx -> Bool ctx
fpIsValid = undefined

--------------------------------------------------------------------------------

toNative :: forall t ctx . Functor t => (t :.: ForeignField) (WitnessField ctx) -> t (WitnessField (ForeignContext ctx))
toNative (Comp1 a) = fmap unPar1 a

fromNative :: forall t ctx . Functor t => t (WitnessField (ForeignContext ctx)) -> (t :.: ForeignField) (WitnessField ctx)
fromNative a = Comp1 $ fmap Par1 a

--------------------------------------------------------------------------------

toWitness :: forall t ctx . (Functor t, Foldable t, Symbolic ctx) => t (FieldElement ctx) -> t (WitnessField ctx)
toWitness = witnessF . packed . fmap fromFieldElement

fromWitness :: forall t ctx . (Traversable t, Symbolic ctx) => t (WitnessField ctx) -> t (FieldElement ctx)
fromWitness = fmap FieldElement . unpacked . embedW

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
    , FiniteField (ForeignField (FieldElement ctx))
    )
    => ForeignPoint algo d k ctx
    -> ForeignOperationInput (WitnessField ctx)
    -> ForeignPoint algo d k ctx
fopCircuit ForeignPoint {..} op =
    let
        -- witness computation

        g :: PrimaryGroup (WitnessField (ForeignContext ctx))
        g = toNative @_ @ctx $ toWitness $ Comp1 $ opRes $ unComp1 fpValue

        input0 :: NativeOperation (WitnessField (ForeignContext ctx))
        input0 = NativeOperation zero zero zero zero zero

        payload :: NativePayload (WitnessField (ForeignContext ctx))
        payload = case toNative @_ @ctx op of
            Addition h       -> NativePayload zero g h    zero
            Multiplication s -> NativePayload s    g zero one

        narkIP :: NARKInstanceProof k NativeOperation SecondaryGroup (ForeignContext ctx)
        narkIP@(NARKInstanceProof input (NARKProof piX _)) = narkInstanceProof (opProtocol @algo @d) input0 payload

        accX :: AccumulatorInstance k NativeOperation SecondaryGroup (WitnessField (ForeignContext ctx))
        accX = toNative @_ @ctx $ toWitness fpAccumulatorInstance

        accW :: Vector k [WitnessField (ForeignContext ctx)]
        accW = unComp1 $ toNative @_ @ctx fpAccumulatorProof

        acc :: Accumulator k NativeOperation SecondaryGroup (WitnessField (ForeignContext ctx))
        acc = Accumulator accX accW

        (acc', pf) = prover (opAccumulatorScheme @algo) acc narkIP

        -- in-circuit computation

        inputC :: NativeOperation (ForeignField (FieldElement ctx))
        inputC = unComp1 $ fromWitness $ fromNative @_ @ctx input

        piXC :: Vector k (SecondaryGroup (ForeignField (FieldElement ctx)))
        piXC = unComp1 $ unComp1 $ fromWitness $ fromNative @_ @ctx $ Comp1 piX

        accXC :: AccumulatorInstance k NativeOperation SecondaryGroup (ForeignField (FieldElement ctx))
        accXC = unComp1 fpAccumulatorInstance

        pfC :: Vector (d-1) (SecondaryGroup (ForeignField (FieldElement ctx)))
        pfC = unComp1 $ unComp1 $ fromWitness $ fromNative @_ @ctx $ Comp1 pf

        accX' :: (AccumulatorInstance k NativeOperation SecondaryGroup :.: ForeignField) (FieldElement ctx)
        accX' = Comp1 $ verifier (opAccumulatorScheme @algo @_ @_ @ctx) @(ForeignField (FieldElement ctx)) inputC piXC accXC pfC

        accW' :: ((Vector k :.: []) :.: ForeignField) (WitnessField ctx)
        accW' = fromNative @_ @ctx $ Comp1 $ acc'^.w

    in ForeignPoint (Comp1 inputC) accX' accW'

--------------------------------------------------------------------------------

instance Haskell.Show (ForeignPoint algo d k ctx) where
    show = const "ForeignPoint"

instance (Haskell.Eq (ctx Par1), Haskell.Eq (WitnessField ctx)) => Haskell.Eq (ForeignPoint algo d k ctx) where
    p == p' = opRes (unComp1 $ fpValue p) Haskell.== opRes (unComp1 $ fpValue p')

instance
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => AdditiveSemigroup (ForeignPoint algo d k ctx) where
    p + p' =
        let
            g :: PrimaryGroup (ForeignField (FieldElement ctx))
            g = opRes $ unComp1 $ fpValue p'

            opi :: ForeignOperationInput (WitnessField ctx)
            opi = toWitness $ Comp1 $ Addition g
        in
            fopCircuit p opi

instance
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => Scale Natural (ForeignPoint algo d k ctx) where
    scale a p =
        let
            s :: PrimaryField (ForeignField (WitnessField ctx))
            s = fromConstant a

            opi :: ForeignOperationInput (WitnessField ctx)
            opi = Comp1 $ Multiplication s
        in
            fopCircuit p opi

instance
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => AdditiveMonoid (ForeignPoint algo d k ctx) where
    zero =
        let
            acc = emptyAccumulator
        in
            ForeignPoint (Comp1 $ opInit zero) (Comp1 $ acc^.x) (toWitness @_ @ctx $ Comp1 $ Comp1 $ acc^.w)

instance
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => Scale Integer (ForeignPoint algo d k ctx) where
    scale a p =
        let
            s :: PrimaryField (ForeignField (WitnessField ctx))
            s = fromConstant a

            opi :: ForeignOperationInput (WitnessField ctx)
            opi = Comp1 $ Multiplication s
        in
            fopCircuit p opi

instance
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => AdditiveGroup (ForeignPoint algo d k ctx) where
    negate = scale (-1 :: Integer)

instance 
    ( HashAlgorithm algo
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , Symbolic ctx
    , Binary (BaseField ctx)
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => Arbitrary (ForeignPoint algo d k ctx) where
    arbitrary = do
        let acc = emptyAccumulator
        s <- fromConstant . toConstant @(Zp BLS12_381_Scalar) <$> arbitrary
        return $ ForeignPoint (Comp1 $ opInit s) (Comp1 $ acc^.x) (toWitness @_ @ctx $ Comp1 $ Comp1 $ acc^.w)
