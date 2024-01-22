{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.Script where

import           Prelude                          (Eq (..), ($), error, otherwise)

import           ZkFold.Symbolic.Compiler
import           ZkFold.Prelude                  (length)

newtype ScriptHash x = ScriptHash x

instance Arithmetizable a x => Arithmetizable a (ScriptHash x) where
    arithmetize (ScriptHash x) = arithmetize x

    restore script
        | length script == typeSize @a @(ScriptHash x) = ScriptHash $ restore script
        | otherwise = error "restore ScriptHash: wrong number of arguments"

    typeSize = typeSize @a @x