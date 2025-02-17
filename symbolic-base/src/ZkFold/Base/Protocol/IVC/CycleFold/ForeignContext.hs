{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.CycleFold.ForeignContext where

import           GHC.Generics                               (Generic)
import           Prelude                                    (return, type (~), ($))
import qualified Prelude                                    as Haskell
import           Test.QuickCheck                            (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class            (AdditiveSemigroup (..), Scale (..), zero, (+))
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (+), type (-))
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.CommitOpen        (commitOpen)
import           ZkFold.Base.Protocol.IVC.FiatShamir        (FiatShamir, fiatShamir)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.SpecialSound      (specialSoundProtocol)
import           ZkFold.Symbolic.Class                      (Arithmetic)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import ZkFold.Symbolic.Data.Class

data NativeOperationInput point
  = Addition point
  | Multiplication (ScalarFieldOf point)

--------------------------------------------------------------------------------

data NativeOperation point = NativeOperation
    { opS   :: ScalarFieldOf point
    , opG   :: point
    , opH   :: point
    , opRes :: point
    , opId  :: BooleanOf point
    }
    deriving (Generic)

instance Haskell.Eq point => Haskell.Eq (NativeOperation point) where
    op1 == op2 = opRes op1 Haskell.== opRes op2

opInit :: (CyclicGroup point, Eq point) => point -> NativeOperation point
opInit init = NativeOperation
    { opS   = zero
    , opG   = zero
    , opH   = zero
    , opRes = init
    , opId  = false
    }

instance
    ( Arbitrary (ScalarFieldOf point)
    , Arbitrary point
    , CyclicGroup point
    , Eq point
    ) => Arbitrary (NativeOperation point) where
    arbitrary = do
        s <- arbitrary
        g <- arbitrary
        h <- arbitrary
        op <- arbitrary
        return $ if op
            then NativeOperation s g h (g + h) false
            else NativeOperation s g h (scale s g) true

--------------------------------------------------------------------------------

data NativePayload point =
  NativePayload (ScalarFieldOf point) point point (BooleanOf point)
    deriving (Generic)

instance
    ( Arbitrary (ScalarFieldOf point)
    , Arbitrary point
    , Eq point
    ) => Arbitrary (NativePayload point) where
    arbitrary = do
        s <- arbitrary
        g <- arbitrary
        h <- arbitrary
        op <- arbitrary
        return $ NativePayload s g h (if op then false else true)

--------------------------------------------------------------------------------

opCircuit :: forall point. (CyclicGroup point, Eq point)
    => NativeOperation point
    -> NativePayload point
    -> NativeOperation point
opCircuit _ (NativePayload s g h op) =
    let
        opS :: ScalarFieldOf point
        opS = s

        opG :: point
        opG = g

        opH :: point
        opH = h

        opId :: BooleanOf point
        opId = op

        opRes :: point
        opRes = ifThenElse opId (scale opS opG) (opG + opH)
    in NativeOperation {..}

type State a = Layout (NativeOperation point)
type Item a = Layout (NativePayload point)

opPredicate :: forall a.
    ( Arithmetic a
    , Binary a
    )
    => Predicate a (State a) (Item a)
opPredicate = predicate \i p -> arithmetize (opCircuit _ _) Proxy

opProtocol :: forall algo d k a point point2.
    ( HashAlgorithm algo
    , KnownNat (d + 1)
    , k ~ 1
    , Arithmetic a
    , Binary a
    )
    => FiatShamir k a (State point) (Item point) (Layout point2)
opProtocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d $ opPredicate @point

opAccumulatorScheme :: forall algo d k a point point2.
    ( HashAlgorithm algo
    , KnownNat (d - 1)
    , KnownNat (d + 1)
    , Arithmetic a
    , Binary a
    )
    => AccumulatorScheme d k a (State point) (Layout point2)
opAccumulatorScheme = accumulatorScheme @algo $ opPredicate @point
