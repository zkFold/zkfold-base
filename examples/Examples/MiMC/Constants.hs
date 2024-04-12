{-# LANGUAGE TypeApplications #-}

module Examples.MiMC.Constants (mimcConstants) where

import           Crypto.Hash.SHA256              (hash)
import           Data.Maybe                      (fromJust)
import           Prelude

import           ZkFold.Base.Algebra.Basic.Class (FromConstant (..))
import           ZkFold.Base.Data.ByteString
import           ZkFold.Symbolic.Types           (I)

mimcSeed :: LittleEndian
mimcSeed = 42

mimcConstants :: forall a . (FromConstant I a) => [a]
mimcConstants =
  let
    getI = fromIntegral . fromJust . fromByteString @LittleEndian
    cs = take 218 $ map getI $ iterate hash $ toByteString mimcSeed
  in map (fromConstant @I @a) (0 : cs ++ [0])
