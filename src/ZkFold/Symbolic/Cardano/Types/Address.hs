{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.Address where

import           Prelude                          (Eq (..), ($), error, otherwise, concat, return)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Prelude                  (length, take, drop)

data Address x = Address
    {
        addrType      :: x,
        addrPayCred   :: x,
        addrStakeCred :: x
    }

instance Arithmetizable a x => Arithmetizable a (Address x) where
    arithmetize (Address addrType payCred stakeCred) = do
        addrType'      <- arithmetize addrType
        payCred'       <- arithmetize payCred
        stakeCred'     <- arithmetize stakeCred
        return $ concat [addrType', payCred', stakeCred']

    restore address
        | length address == typeSize @a @(Address x) =
            let addrType'      = restore $ take (typeSize @a @x) address
                payCred'       = restore $ take (typeSize @a @x) $ drop (typeSize @a @x) address
                stakeCred'     = restore $ drop (2 * typeSize @a @x) address
            in Address addrType' payCred' stakeCred'
        | otherwise = error "restore Address: wrong number of arguments"

    typeSize = 3 * typeSize @a @x