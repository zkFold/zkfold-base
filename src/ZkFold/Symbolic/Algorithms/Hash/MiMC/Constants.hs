module ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants) where

import           Crypto.Hash.SHA256              (hash)
import           Data.Maybe                      (fromJust)
import           Prelude
import           Numeric.Natural                 (Natural)

import           ZkFold.Base.Algebra.Basic.Class (FromConstant (..))
import           ZkFold.Base.Data.ByteString

mimcSeed :: LittleEndian
mimcSeed = 42

-- | The round constants ci are random elements of F_2n except for the first and
--   last round constants which are equal to 0.
--
mimcConstants :: forall a . (FromConstant Natural a) => [a]
mimcConstants =
  let
    getN = unLittleEndian . fromJust . fromByteString @LittleEndian
    cs = take 218 $ map getN $ iterate hash $ toByteString mimcSeed
  in map (fromConstant @Natural @a) (0 : cs ++ [0])
