{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Algebra.Symbolic.Class where

import           Prelude                   (Monoid (..), undefined)

-- | A class for symbolic computations.
-- The first argument is the symbolic computation context. It contains symbolic variables and relations between them.
-- The second argument is the type of object for which we want to compute a symbolic representation.
class Monoid ctx => Symbolic ctx t where
    {-# MINIMAL symbolic', symInput, symVar, eval #-}

    -- | The value of the object.
    type ValueOf t

    -- | Computes the symbolic representation using the supplied symbolic computation context.
    symbolic' :: t -> ctx -> ctx

    -- | Computes the symbolic representation using the empty symbolic computation context.
    symbolic  :: t -> ctx
    symbolic x = symbolic' x mempty

    -- | Constructs a new symbolic input object from the given symbolic computation context.
    symInput  :: ctx -> t

    -- | Constructs a new symbolic variable from the given symbolic computation context.
    symVar    :: ctx -> t

    -- | Evaluates the symbolic representation using the supplied value.
    eval      :: ctx -> ValueOf t -> ctx

instance (Symbolic ctx f, Symbolic ctx a) => Symbolic ctx (a -> f) where
    type ValueOf (a -> f) = ValueOf a -> ValueOf f

    symbolic' f ctx =
        let x = symInput ctx
        in symbolic' (f x) (symbolic' @ctx @a x ctx)
    
    -- TODO: complete this definition
    symInput = undefined

    -- TODO: complete this definition
    symVar = undefined

    -- TODO: complete this definition
    eval = undefined