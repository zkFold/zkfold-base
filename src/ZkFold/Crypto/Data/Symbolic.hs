{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Data.Symbolic where

import           Prelude                   (Integer, head)

-- | A class for symbolic variables.
-- We want to describe a value of type `t` using a list of values of type `a`.
-- A symbolic variable that corresponds to type `t` is of type `s`.
-- It can be converted to and obtained from a list of integers.
-- Each integer number represents an atomic symbolic variable whose value is of type `a`.
class Symbolic a t s | t -> s where
    fromValue  :: t -> [a]

    toValue    :: [a] -> t

    fromSymbol :: s -> [Integer]

    toSymbol   :: [Integer] -> s

    symbolSize :: Integer

instance Symbolic a a Integer where
    fromValue  = (: [])

    toValue    = head

    fromSymbol = (: [])

    toSymbol   = head

    symbolSize = 1