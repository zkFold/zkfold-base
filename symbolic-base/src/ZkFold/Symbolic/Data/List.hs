{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Data.List where

import           Control.Applicative              (Applicative)
import           Data.Bifunctor                   (first)
import           Data.Function                    (const)
import           Data.Functor.Rep                 (Representable, pureRep)
import           Data.Proxy                       (Proxy (..))
import           Data.Traversable                 (Traversable)
import           Data.Zip                         (Zip)
import           GHC.Generics                     (Par1 (..))
import           Prelude                          (fmap, fst, pure, type (~), undefined, ($), (.), (<$>))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Utils           (zipWithM)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.MonadCircuit

data List c x = List
  { lHash    :: c (Layout x)
  , lSize    :: c Par1
  , lWitness :: [(Layout x (WitnessField c), Support x -> (Layout x (WitnessField c), Payload x (WitnessField c)))]
  -- ^ TODO: As the name suggests, this is only needed in witness cinstruction in uncons.
  -- This list is never used in circuit itlest.
  -- Think of a better solution for carrying witnesses.
  -- Besides, List is not an instance of SymbolicData while this list is present
  }

-- | TODO: A proof-of-concept where hash == id.
-- Replace id with a proper hash if we need lists to be cryptographically secure.
--
emptyList
    :: forall context x
    .  Symbolic context
    => Applicative (Layout x)
    => List context x
emptyList = List (embed $ pure zero) (embed $ Par1 zero) []

-- | A list is empty if it's size is 0, in which case the first element of @runInvert@ is @one@.
--
null
    :: forall context x
    .  Symbolic context
    => List context x
    -> Bool context
null List{..} = Bool (fromCircuitF lSize (fmap fst . runInvert))

infixr 5 .:
(.:)
    :: forall context x
    .  Symbolic context
    => Traversable (Layout x)
    => Zip (Layout x)
    => SymbolicData x
    => Context x ~ context
    => Support x ~ Proxy context
    => x
    -> List context x
    -> List context x
x .: List{..} = List incSum incSize ((witnessF lHash, \s -> (witnessF (arithmetize x s), payload x s)):lWitness)
    where
        xRepr :: context (Layout x)
        xRepr = arithmetize x (Proxy @context)

        incSum :: context (Layout x)
        incSum = fromCircuit3F lHash xRepr lSize $
            \vHash vRepr (Par1 s) -> zipWithM (\h r -> newAssigned (\p -> p h + p r * (p s + one))) vHash vRepr

        incSize :: context Par1
        incSize = fromCircuitF lSize (\(Par1 s) -> Par1 <$> newAssigned (\p -> p s + one))

uncons
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Applicative (Layout x)
    => Traversable (Layout x)
    => Representable (Layout x)
    => Zip (Layout x)
    => SymbolicData (List context x) -- TODO: Implement this
    => Representable (Layout (List context x))
    => Traversable (Layout (List context x))
    => Context x ~ context
    => Context (List context x) ~ context
    => Support x ~ Proxy context
    => List context x
    -> (x, List context x)
uncons l = (head l, tail l)

-- | TODO: Is there really a nicer way to handle empty lists?
--
head
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Context x ~ context
    => List context x -> x
head l = case lWitness l of
  []    -> restore $ const (embed (pureRep zero), pureRep zero)
  (w:_) -> restore $ first _ . w

tail
    :: forall context x
    .  Symbolic context
    => Applicative (Layout x)
    => Traversable (Layout x)
    => Zip (Layout x)
    => SymbolicData x
    => SymbolicData (List context x) -- TODO: Implement this
    => Representable (Layout (List context x))
    => Traversable (Layout (List context x))
    => Context x ~ context
    => Context (List context x) ~ context
    => Support x ~ Proxy context
    => List context x
    -> List context x
tail xs@List{..} = bool unsafeTail xs (null xs)
    where
        tailId :: [a] -> [a]
        tailId []      = []
        tailId (_:xs') = xs'

        unsafeTail :: List context x
        unsafeTail = List decSum decSize (tailId lWitness)

        xRepr :: context (Layout x)
        xRepr = case lWitness of
                  (x:_) -> arithmetize x Proxy
                  _     -> embed $ pure zero

        decSum :: context (Layout x)
        decSum = fromCircuit3F lHash xRepr lSize $
            \vHash vRepr (Par1 s) -> zipWithM (\h r -> newAssigned (\p -> p h - p r * p s)) vHash vRepr

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
last :: List context x -> x
last = undefined

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
