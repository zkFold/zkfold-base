module ZkFold.Base.Protocol.Plonkup.LookupConstraint where

import           Data.Binary                                         (Binary)
import           Data.ByteString                                     (ByteString)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Data.ByteString                         (toByteString)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

newtype LookupConstraint i a = LookupConstraint { lkVar :: SysVar (Vector i) }
    deriving (Show, Eq)

instance (Arbitrary a, Binary a) => Arbitrary (LookupConstraint i a) where
    arbitrary = LookupConstraint . NewVar . toByteString @a <$> arbitrary

toLookupConstraint :: forall a i . ByteString -> LookupConstraint i a
toLookupConstraint = LookupConstraint . NewVar
