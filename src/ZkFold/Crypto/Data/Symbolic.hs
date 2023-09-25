{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Data.Symbolic where

import           Control.Monad.State       (State, execState, MonadState (..))
import           Prelude                   (Monoid (..), undefined)

-- | A class for symbolic computations.
-- The first argument is the symbolic computation context. It contains symbolic variables and relations between them.
-- The second argument is the type of object for which we want to compute a symbolic representation.
class Monoid ctx => Symbolic ctx t where
    {-# MINIMAL merge, assignment, apply, constraint, input, extract, eval #-}

    -- | The value of the object.
    type ValueOf t

    type InputOf t

    type WitnessMap ctx t

    type Constraint ctx t

    -- | Computes the symbolic representation using the supplied symbolic computation context.
    merge      :: t -> State ctx ctx

    -- | Computes the symbolic representation using the empty symbolic computation context.
    compile    :: t -> ctx
    compile x = execState (merge x) mempty

    assignment :: WitnessMap ctx t -> State ctx ()

    -- | Evaluates the symbolic representation using the supplied value.
    apply      :: ctx -> ValueOf t -> ctx
    -- apply ctx x = assignment ctx $ inputMap ctx x

    constraint :: Constraint ctx t -> State ctx ()

    -- | Constructs a new symbolic input object from the given symbolic computation context.
    input      :: ctx -> t

    -- | Constructs a new symbolic variable from the given symbolic computation context.
    extract    :: ctx -> t

    eval       :: ctx -> InputOf t -> ValueOf t

instance (Symbolic ctx f, Symbolic ctx a) => Symbolic ctx (a -> f) where
    type ValueOf (a -> f) = ValueOf a -> ValueOf f

    type InputOf (a -> f) = InputOf f

    type WitnessMap ctx (a -> f) = ()

    type Constraint ctx (a -> f) = ()

    merge f = do
        ctx <- get
        let x = input ctx
        _ <- merge x
        merge (f x)

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