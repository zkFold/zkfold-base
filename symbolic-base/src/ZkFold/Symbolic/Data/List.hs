{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Data.List where

import           Data.Kind                        (Type)
import           Data.Proxy                       (Proxy (..))
import           GHC.Generics                     (Par1 (..))
import           Prelude                          (flip, fmap, fst, pure, undefined, ($), (.), (<$>))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Par1
import qualified ZkFold.Base.Data.Vector          as V
import           ZkFold.Base.Data.Vector          (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.MonadCircuit

data List (context :: (Type -> Type) -> Type) x
    = List
        { lHash    :: (context (Vector (TypeSize x)))
        , lSize    :: (context Par1)
        , lWitness :: [x]
        -- ^ TODO: As the name suggests, this is only needed in witness cinstruction in uncons.
        -- This list is never used in circuit itlest.
        -- Think of a better solution for carrying witnesses.
        -- Besides, List is not an instance of SymbolicData while this list is present
        }

-- | TODO: A proof-of-concept where hash == id.
-- Replace id with a proper hash if we need lists to be cryptographically secure.
--
emptyList :: forall context x . (Symbolic context, SymbolicData x, KnownNat (TypeSize x)) => List context x
emptyList = List (embed $ pure zero) (embed $ Par1 zero) []

-- | A list is empty if it's size is 0, in which case the first element of @runInvert@ is @one@.
--
null
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => List context x
    -> Bool context
null List{..} = Bool (fromCircuitF lSize (fmap fst . runInvert))

infixr 5 .:
(.:)
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Layout x ~ Vector (TypeSize x)
    => Context x ~ context
    => Support x ~ Proxy context
    => x
    -> List context x
    -> List context x
x .: List{..} = List incSum incSize (x:lWitness)
    where
        xRepr :: context (Vector (TypeSize x))
        xRepr = pieces x (Proxy @context)

        incSum :: context (Vector (TypeSize x))
        incSum = fromCircuit3F lHash xRepr lSize $
            \vHash vRepr (Par1 s) -> V.zipWithM (\h r -> newAssigned (\p -> p h + p r * (p s + one))) vHash vRepr

        incSize :: context Par1
        incSize = fromCircuitF lSize (\(Par1 s) -> Par1 <$> newAssigned (\p -> p s + one))

uncons
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Layout x ~ Vector (TypeSize x)
    => Context x ~ context
    => Context (List context x) ~ context
    => Support x ~ Proxy context
    => KnownNat (TypeSize x)
    => List context x
    -> (x, List context x)
uncons l = (head l, tail l)

-- | TODO: Is there really a nicer way to handle empty lists?
--
head
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Layout x ~ Vector (TypeSize x)
    => Context x ~ context
    => Support x ~ Proxy context
    => KnownNat (TypeSize x)
    => List context x -> x
head xs@List{..} = bool (restore $ \_ -> unsafeHead) (restore $ \_ -> embed $ pure zero) (null xs)
    where
        xRepr :: context (Vector (TypeSize x))
        xRepr = case lWitness of
                  (x:_) -> pieces x Proxy
                  _     -> embed $ pure zero

        -- | Head is a circuit comprised of variables satisfying the equation for prepending (i.e. (.:))
        -- We have to pass witnesses to it as well.
        --
        unsafeHead :: context (Vector (TypeSize x))
        unsafeHead = fromCircuit3F lHash xRepr lSize $
            \vHash vRepr (Par1 s) -> V.zipWithM (\h r -> newConstrained (\p v -> p h + p v * (p s + one)) ($ r)) vHash vRepr

tail
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Layout x ~ Vector (TypeSize x)
    => Layout (List context x) ~ Vector (TypeSize x + 1)
    => Context x ~ context
    => Context (List context x) ~ context
    => Support x ~ Proxy context
    => KnownNat (TypeSize x)
    => List context x
    -> List context x
tail xs@List{..} = bool unsafeTail xs (null xs)
    where
        tailId :: [a] -> [a]
        tailId []     = []
        tailId (_:xs) = xs

        unsafeTail :: List context x
        unsafeTail = List decSum decSize (tailId lWitness)

        xRepr :: context (Vector (TypeSize x))
        xRepr = case lWitness of
                  (x:_) -> pieces x Proxy
                  _     -> embed $ pure zero

        decSum :: context (Vector (TypeSize x))
        decSum = fromCircuit3F lHash xRepr lSize $
            \vHash vRepr (Par1 s) -> V.zipWithM (\h r -> newAssigned (\p -> p h - p r * p s)) vHash vRepr

        decSize :: context Par1
        decSize = fromCircuitF lSize (\(Par1 s) -> Par1 <$> newAssigned (\p -> p s - one))

{-- TODO: Foldable relies on Haskell types such as Bool (i.e. null = foldr (\_ _ -> False) True)
   I am not sure this is suitable for Symbolic interface

reverse :: forall context x . Foldable (List context) => List context x -> List context x
reverse = foldl (flip (.:)) emptyList

init :: forall context x . Foldable (List context) => List context x -> List context x
init = reverse . tail . reverse

last :: forall context x . Foldable (List context) => List context x -> x
last = head . reverse
--}

(++) :: List context x -> List context x -> List context x
_ ++ _ = undefined

filter ::
       (x -> Bool context)
    -> List context x
    -> List context x
filter = undefined

delete :: x -> List context x -> List context x
delete = undefined

(\\) :: List context x -> List context x -> List context x
_ \\ _ = undefined
