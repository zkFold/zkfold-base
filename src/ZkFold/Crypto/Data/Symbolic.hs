{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Data.Symbolic where

import           Control.Monad.State       (State, execState)
import           Prelude                   (Monoid (..), Integer, undefined, head)

class SymbolicVariable a t where
    type SymbolOf t

    fromValue  :: t -> [a]

    toValue    :: [a] -> t

    fromSymbol :: SymbolOf t -> [Integer]

    toSymbol   :: [Integer] -> SymbolOf t

    symbolSize :: Integer

instance SymbolicVariable a a where
    type SymbolOf a = Integer

    fromValue  = (: [])

    toValue    = head

    fromSymbol = (: [])

    toSymbol   = head

    symbolSize = 1

-- | A class for symbolic computations.
-- The first argument is the symbolic computation context. It contains symbolic variables and relations between them.
-- The second argument is the type of object for which we want to compute a symbolic representation.
class Monoid ctx => Symbolic ctx t where
    {-# MINIMAL merge, atomic, constraint, assignment, eval, input, current, apply #-}

    -- | The value of the object.
    type ValueOf t

    type InputOf t

    type Constraint ctx t

    -- | Computes the symbolic representation using the supplied symbolic computation context.
    merge      :: t -> State ctx ctx

    atomic     :: ctx -> [ctx]

    -- | Computes the symbolic representation using the empty symbolic computation context.
    compile    :: t -> ctx
    compile x = execState (merge x) mempty

    constraint :: Constraint ctx t -> State ctx ()

    assignment :: (InputOf t -> ValueOf t) -> State ctx ()

    eval       :: ctx -> InputOf t -> ValueOf t

    -- | Constructs a new symbolic input object from the given symbolic computation context.
    input      :: State ctx t

    -- | Constructs a new symbolic variable from the given symbolic computation context.
    current    :: State ctx t

    -- | Evaluates the symbolic representation using the supplied value.
    apply      :: ValueOf t -> State ctx ()

instance (Symbolic ctx f, Symbolic ctx a) => Symbolic ctx (a -> f) where
    type ValueOf (a -> f) = ValueOf a -> ValueOf f

    type InputOf (a -> f) = InputOf f

    type Constraint ctx (a -> f) = ()

    merge f = do
        x <- input
        _ <- merge x
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