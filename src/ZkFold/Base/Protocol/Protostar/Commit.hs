module ZkFold.Base.Protocol.ARK.Protostar.Commit (Commit (..)) where

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Protocol.ARK.Protostar.Oracle

-- | Commit to the object @a@ with commitment key @ck@ and results of type @f@
--
class Commit ck a f where
    commit :: ck -> a -> f

instance (RandomOracle ck x, RandomOracle a x, Ring x) => Commit ck a x where
    commit ck a = oracle [oracle @ck @x ck, oracle @a @x a]
