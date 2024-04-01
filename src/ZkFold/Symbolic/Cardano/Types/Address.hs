{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Cardano.Types.Address where


import           Prelude                  hiding ((*), length, splitAt)
import           Control.Monad.State.Lazy        (evalState, state)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Prelude                  (length, splitAt)

data Address x = Address
    { addrType :: x
    , addrPayCred :: x
    , addrStakeCred :: x
    } deriving Eq

instance Arithmetizable a x => Arithmetizable a (Address x) where
    arithmetize (Address addrType payCred stakeCred) =
        (\t p s -> t <> p <> s)
            <$> arithmetize addrType
            <*> arithmetize payCred
            <*> arithmetize stakeCred
    restore address =
        if length address == typeSize @a @(Address x)
        then flip evalState address $ Address
            <$> do restore <$> do state . splitAt $ typeSize @a @x
            <*> do restore <$> do state . splitAt $ typeSize @a @x
            <*> do restore <$> do state . splitAt $ typeSize @a @x
        else error "restore Address: wrong number of arguments"
    typeSize = 3 * typeSize @a @x
