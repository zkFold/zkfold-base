{-# LANGUAGE TypeApplications #-}

module ZkFold.Cardano.Types.Script where

import           Prelude                          (Eq (..), ($), error, otherwise)

import           ZkFold.Symbolic.Arithmetization (Arithmetizable(..))
import           ZkFold.Prelude                  (length)

newtype Script x = Script x

instance Arithmetizable a x => Arithmetizable a (Script x) where
    arithmetize (Script x) = arithmetize x

    restore script
        | length script == typeSize @a @(Script x) = Script $ restore script
        | otherwise = error "restore Script: wrong number of arguments"

    typeSize = typeSize @a @x