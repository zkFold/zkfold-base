{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Crypto.Data.Symbolic where

import           Prelude                   (Monoid (..), undefined)

-- | A class for symbolic computations.
-- The first argument is the symbolic computation context. It contains symbolic variables and relations between them.
-- The second argument is the type of object for which we want to compute a symbolic representation.
class Monoid ctx => Symbolic ctx t where
    {-# MINIMAL merge, assignment, apply, constraint, input, extract, eval #-}

    -- | The value of the object.
    type ValueOf t

    type InputMap ctx t

    type WitnessMap ctx t

    type Constraint ctx t

    -- | Computes the symbolic representation using the supplied symbolic computation context.
    merge      :: t -> ctx -> ctx

    -- | Computes the symbolic representation using the empty symbolic computation context.
    compile    :: t -> ctx
    compile x = merge x mempty

    assignment :: ctx -> WitnessMap ctx t -> ctx

    -- | Evaluates the symbolic representation using the supplied value.
    apply      :: ctx -> ValueOf t -> ctx
    -- apply ctx x = assignment ctx $ inputMap ctx x

    constraint :: ctx -> Constraint ctx t -> ctx

    -- | Constructs a new symbolic input object from the given symbolic computation context.
    input      :: ctx -> t

    -- | Constructs a new symbolic variable from the given symbolic computation context.
    extract    :: ctx -> t

    eval       :: ctx -> ValueOf t

instance (Symbolic ctx f, Symbolic ctx a) => Symbolic ctx (a -> f) where
    type ValueOf (a -> f) = ValueOf a -> ValueOf f

    type InputMap ctx (a -> f) = ()

    type WitnessMap ctx (a -> f) = ()

    type Constraint ctx (a -> f) = ()

    merge f ctx =
        let x = input ctx
        in merge (f x) (merge @ctx @a x ctx)
    
    -- TODO: complete this definition
    assignment = undefined

    -- TODO: complete this definition
    apply = undefined

    -- TODO: complete this definition
    constraint = undefined

    -- TODO: complete this definition
    input = undefined

    -- TODO: complete this definition
    extract = undefined

    -- TODO: complete this definition
    eval = undefined