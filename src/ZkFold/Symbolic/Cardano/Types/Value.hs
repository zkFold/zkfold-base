{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.Value where

import           Prelude                         (Eq (..), ($), error, otherwise, concat, return, mapM, (++), map)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.UInt       (UInt32)
import           ZkFold.Prelude                  (length, take, drop)

newtype Value size x = Value [(x, x, UInt32 x)]

instance (Arithmetizable a x, Finite size) => Arithmetizable a (Value size x) where
    arithmetize (Value value) = do
        value' <- mapM (\(p, s, n) -> do
            p' <- arithmetize p
            s' <- arithmetize s
            n' <- arithmetize n
            return $ p' ++ s' ++ n') value
        return $ concat value'

    restore value
        | length value == typeSize @a @(Value size x) =
            Value $ map (\i -> restore $ take (3 * typeSize @a @x) $ drop (3 * i * typeSize @a @x) value) [0..(order @size - 1)]
        | otherwise = error "restore Value: wrong number of arguments"

    typeSize = 3 * order @size * typeSize @a @x
