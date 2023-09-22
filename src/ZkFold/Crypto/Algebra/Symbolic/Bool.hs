{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Algebra.Symbolic.Bool (
    SymbolicEq(..),
    SymbolicBool    
) where

import           Prelude                               hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Symbolic.Class

class SymbolicEq b a where
    ($==$) :: a -> a -> b

    ($/=$) :: a -> a -> b

    symTrue :: b
    
    symFalse :: b

    symNot :: b -> b

    symIf :: b -> a -> a -> a

instance Eq a => SymbolicEq Bool a where
    x $==$ y = x == y
    x $/=$ y = x /= y

    symTrue = True
    symFalse = False

    symNot = not

    symIf b t f = if b then t else f

newtype SymbolicBool ctx = SymbolicBool ctx
    deriving (Show)

instance (Symbolic ctx a, FiniteField ctx) => SymbolicEq (SymbolicBool ctx) a where
    x $==$ y =
        let z = symbolic x - symbolic y
        in SymbolicBool $ one - z / z

    x $/=$ y =
        let z = symbolic x - symbolic y
        in SymbolicBool $ z / z
    
    symTrue = SymbolicBool one

    symFalse = SymbolicBool zero

    symNot (SymbolicBool b) = SymbolicBool $ one - b

    symIf (SymbolicBool b) t f =
        let t' = symbolic' t b
            f' = symbolic' f b
        in symVar $ b * t' + (one - b) * f'