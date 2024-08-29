module ZkFold.Base.Protocol.Plonkup.LookupConstraint where

import           GHC.TypeNats                                        (KnownNat)
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

newtype LookupConstraint i a = LookupConstraint { lkVar :: Var (Vector i) }
    deriving (Show, Eq)

instance (Arbitrary a, Finite a, ToConstant a Natural, KnownNat i) => Arbitrary (LookupConstraint i a) where
    arbitrary = LookupConstraint . NewVar . toConstant @a <$> arbitrary

toLookupConstraint :: forall a i . Natural -> LookupConstraint i a
toLookupConstraint = LookupConstraint . NewVar