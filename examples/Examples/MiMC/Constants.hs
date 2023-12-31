{-# LANGUAGE TypeApplications    #-}

module Examples.MiMC.Constants (mimcConstants) where

import           Crypto.Hash.SHA256              (hash)
import           Data.Maybe                      (fromJust)
import           Prelude                        

import           ZkFold.Base.Algebra.Basic.Class (FromConstant(..))
import           ZkFold.Base.Data.ByteString     (ToByteString(..), FromByteString (..))
import           ZkFold.Symbolic.Types           (I)

mimcSeed :: Integer
mimcSeed = 42

mimcConstants :: forall a . (FromConstant I a) => [a]
mimcConstants = 
  let cs = take 218 $ map (fromJust . fromByteString) $ iterate hash $ toByteString mimcSeed
  in map (fromConstant @I @a) (0 : cs ++ [0])