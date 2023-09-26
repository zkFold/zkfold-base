{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Data.Arithmetization where

import           Control.Monad.State       (State, execState)
import           Prelude                   (Monoid (..), undefined)

-- | A class for arithmetization algorithms.
-- Type `ctx` represents the context, i.e. the already computed part of the arithmetic circuit.
-- Type `t` represents the current symbolic variable.
class Monoid ctx => Arithmetization ctx t where
    {-# MINIMAL merge, atomic, constraint, assignment, eval, input, current, apply #-}

    -- | The value of the current variable.
    type ValueOf t

    -- | The type that represents the input in the arithmetic circuit.
    type InputOf t

    -- | The type that represents the constraints in the arithmetic circuit.
    type Constraint ctx t

    -- | Arithmetizes the current symbolic variable and merges it into the current context.
    merge      :: t -> State ctx ()

    -- | Arithmetizes the current symbolic variable starting from an empty context.
    compile    :: t -> ctx
    compile x = execState (merge x) mempty

    -- | Splits the current symbolic variable into atomic symbolic variables preserving the context.
    atomic     :: ctx -> [ctx]

    -- | Adds a constraint to the current context.
    constraint :: Constraint ctx t -> State ctx ()

    -- | Assigns the current symbolic variable to the given symbolic computation.
    assignment :: (InputOf t -> ValueOf t) -> State ctx ()

    -- | Evaluates the arithmetic circuit using the supplied input.
    eval       :: ctx -> InputOf t -> ValueOf t

    -- | Constructs a new symbolic variable of type `t` within the given context.
    input      :: State ctx t

    -- | Returns the current symbolic variable.
    current    :: State ctx t

    -- | Applies the value of the first input argument to the current context.
    apply      :: ValueOf t -> State ctx ()

instance (Arithmetization ctx f, Arithmetization ctx a) => Arithmetization ctx (a -> f) where
    type ValueOf (a -> f) = ValueOf a -> ValueOf f

    type InputOf (a -> f) = InputOf f

    type Constraint ctx (a -> f) = ()

    merge f = do
        x <- input
        merge x
        merge (f x)

    -- TODO: complete this definition
    atomic = undefined

    -- TODO: complete this definition
    constraint = undefined

    -- TODO: complete this definition
    assignment = undefined

    -- TODO: complete this definition
    eval = undefined

    -- TODO: complete this definition
    input = undefined

    -- TODO: complete this definition
    current = undefined

    -- TODO: complete this definition
    apply = undefined