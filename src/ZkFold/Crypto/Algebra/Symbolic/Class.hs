{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Algebra.Symbolic.Class where

import           Prelude                   ((.), const)

-- | A class for symbolic computations.
-- The first argument is the type of the symbolic object.
-- The second argument is the type of the object for which we want to compute the symbolic object.
class Symbolic a f where
    -- | Computes the symbolic object.
    -- The first argument is the object for which we want to compute the symbolic object.
    -- The second argument is the symbolic computation context.
    symbolic  :: f -> a -> a

    -- | Constructs an object from the symbolic computation context.
    newSymbol :: a -> f

instance (Symbolic a f, Symbolic a b) => Symbolic a (b -> f) where
    symbolic f ctx =
        let x = newSymbol ctx
        in symbolic (f x) (symbolic @a @b x ctx)
    
    newSymbol = const . newSymbol @a @f