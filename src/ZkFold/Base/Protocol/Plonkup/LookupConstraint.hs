module ZkFold.Base.Protocol.Plonkup.LookupConstraint where

import           Data.Binary                                         (Binary, encode)
import           Data.ByteString                                     (ByteString, toStrict)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

newtype LookupConstraint i a = LookupConstraint { lkVar :: Var (Vector i) }
    deriving (Show, Eq)

instance (Arbitrary a, Binary a) => Arbitrary (LookupConstraint i a) where
    arbitrary = LookupConstraint . NewVar . toStrict . encode @a <$> arbitrary

toLookupConstraint :: forall a i . ByteString -> LookupConstraint i a
toLookupConstraint = LookupConstraint . NewVar
