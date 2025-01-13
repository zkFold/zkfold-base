{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Internal where

import           Data.Constraint                                     (withDict)
import           Data.Constraint.Nat                                 (plusNat, timesNat)
import           Data.Functor.Classes                                (Show1)
import           Data.Functor.Rep                                    (Rep)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Univariate          (PolyVec)
import           ZkFold.Base.Protocol.Plonkup.Utils
import           ZkFold.Symbolic.Compiler                            ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

{-
    NOTE: we need to parametrize the type of transcripts because we use BuiltinByteString on-chain and ByteString off-chain.
    Additionally, we don't want this library to depend on Cardano libraries.
-}

data Plonkup p i (n :: Natural) l f g1 g2 transcript = Plonkup {
        omega :: f,
        k1    :: f,
        k2    :: f,
        ac    :: ArithmeticCircuit f p i l,
        x     :: f
    }

type PlonkupPermutationSize n = 3 * n

-- The maximum degree of the polynomials we need in the protocol is `4 * n + 5`.
type PlonkupPolyExtendedLength n = 4 * n + 6

with4n6 :: forall n {r}. KnownNat n => (KnownNat (4 * n + 6) => r) -> r
with4n6 f = withDict (timesNat @4 @n) (withDict (plusNat @(4 * n) @6) f)

type PlonkupPolyExtended n f = PolyVec f (PlonkupPolyExtendedLength n)

instance (Show f, Show (Rep i), Show1 l, Ord (Rep i)) => Show (Plonkup p i n l f g1 g2 t) where
    show Plonkup {..} =
        "Plonkup: " ++ show omega ++ " " ++ show k1 ++ " " ++ show k2 ++ " " ++ show (acOutput ac)  ++ " " ++ show ac ++ " " ++ show x

instance
  ( KnownNat n, Arithmetic f, Arbitrary f
  , Arbitrary (ArithmeticCircuit f p i l)
  ) => Arbitrary (Plonkup p i n l f g1 g2 t) where
    arbitrary = do
        ac <- arbitrary
        let (omega, k1, k2) = getParams (value @n)
        Plonkup omega k1 k2 ac <$> arbitrary
