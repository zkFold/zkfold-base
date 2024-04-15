module ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants) where

import           Crypto.Hash.SHA256              (hash)
import           Data.Maybe                      (fromJust)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Class (FromConstant (..))
import           ZkFold.Base.Data.ByteString     (FromByteString (..), ToByteString (..))
import           ZkFold.Symbolic.Types           (I)

mimcSeed :: Integer
mimcSeed = 42

-- | The round constants ci are random elements of F_2n except for the first and
--   last round constants which are equal to 0.
--
mimcConstants :: forall a . (FromConstant I a) => [a]
mimcConstants =
  let cs = take 218 $ map (fromJust . fromByteString) $ iterate hash $ toByteString mimcSeed
  in map (fromConstant @I @a) (0 : cs ++ [0])
