{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Data.Symbolic where

import           Prelude                   (Integer, head)

-- | A class for symbolic variables.
-- We want to describe a value of type `t` using a list of values of type `a`.
-- A symbolic variable is a list of integer numbers.
-- Each integer number represents an atomic symbolic variable whose value is of type `a`.
class Symbolic a t where
    type SymbolOf t

    fromValue  :: t -> [a]

    toValue    :: [a] -> t

    fromSymbol :: SymbolOf t -> [Integer]

    toSymbol   :: [Integer] -> SymbolOf t

    symbolSize :: Integer

instance Symbolic a a where
    type SymbolOf a = Integer

    fromValue  = (: [])

    toValue    = head

    fromSymbol = (: [])

    toSymbol   = head

    symbolSize = 1