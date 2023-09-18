{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Algebra.Symbolic.Class where

import           Prelude                   (Monoid (..), (.), const)

-- | A class for symbolic computations.
-- The first argument is the symbolic computation context. It contains symbolic variables and relations between them.
-- The second argument is the type of object for which we want to compute a symbolic representation.
class Monoid ctx =>  Symbolic ctx t where
    {-# MINIMAL symbolic', newSymbol, substitute #-}

    type SymbolOf ctx t

    type ValueOf t

    -- | Computes the symbolic representation using the supplied symbolic computation context.
    symbolic'  :: t -> ctx -> ctx

    -- | Computes the symbolic representation using the empty symbolic computation context.
    symbolic   :: t -> ctx
    symbolic x = symbolic' x mempty

    -- | Constructs a new object from the given symbolic computation context.
    newSymbol  :: ctx -> t

    -- | Substitutes the given symbolic variable with the given value in the given symbolic computation context.
    substitute :: ctx -> SymbolOf ctx t -> ValueOf t -> ctx

instance (Symbolic ctx f, Symbolic ctx a) => Symbolic ctx (a -> f) where
    type SymbolOf ctx (a -> f) = SymbolOf ctx a
    
    type ValueOf (a -> f) = ValueOf a

    symbolic' f ctx =
        let x = newSymbol ctx
        in symbolic' (f x) (symbolic' @ctx @a x ctx)
    
    newSymbol = const . newSymbol @ctx @f

    substitute ctx x v = substitute @ctx @a ctx x v