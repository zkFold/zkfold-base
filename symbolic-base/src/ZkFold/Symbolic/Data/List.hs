{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Data.List where

import           Control.Monad                    (return)
import           Data.Function                    (const)
import           Data.Functor.Rep                 (Representable, pureRep, tabulate)
import           Data.Proxy                       (Proxy (..))
import           Data.Traversable                 (traverse)
import           Data.Tuple                       (snd)
import           GHC.Generics                     (Par1 (..), (:*:) (..))
import           Prelude                          (fmap, fst, type (~), undefined, ($), (.), (<$>))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.HFunctor        (hmap)
import           ZkFold.Base.Data.Product         (fstP, sndP)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt        (UInt)
import           ZkFold.Symbolic.MonadCircuit

data List c x = List
  { lHash    :: c (Layout x)
  , lSize    :: c Par1
  , lWitness :: [(Layout x (WitnessField c), Layout x (WitnessField c), Payload x (WitnessField c))]
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
    => Representable (Layout x)
    => List context x
emptyList = List (embed $ pureRep zero) (embed $ Par1 zero) []

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
    => SymbolicData x
    => Context x ~ context
    => Support x ~ Proxy context
    => x
    -> List context x
    -> List context x
x .: List{..} = List incSum incSize ((witnessF lHash, witnessF (arithmetize x Proxy), payload x Proxy):lWitness)
    where
        xRepr :: context (Layout x)
        xRepr = arithmetize x (Proxy @context)

        incSize :: context Par1
        incSize = fromCircuitF lSize (\(Par1 s) -> Par1 <$> newAssigned (\p -> p s + one))

        incSum :: context (Layout x)
        incSum = fromCircuit3F lHash xRepr incSize $
            \vHash vRepr (Par1 s) -> mzipWithMRep (hashF s) vHash vRepr

hashF :: MonadCircuit i a w m => i -> i -> i -> m i
hashF s h t = newAssigned (($ h) + ($ t) * ($ s))

uncons ::
  forall c x.
  (Symbolic c, SymbolicData x) =>
  (Context x ~ c, Support x ~ Proxy c, Representable (Payload x)) =>
  List c x -> (x, List c x)
uncons l@List{..} = case lWitness of
  [] -> (restore $ const (lHash, tabulate (const zero)), l)
  ((tHash, hdL, hdP):tWitness) ->
    ( restore $ const (hmap fstP preimage, hdP)
    , List (hmap sndP preimage) decSize tWitness)
    where
      decSize = fromCircuitF lSize $ \(Par1 i) ->
        Par1 <$> newAssigned (($ i) - one)

      preimage :: c (Layout x :*: Layout x)
      preimage = fromCircuit2F lSize lHash $ \(Par1 s) y -> do
        tH :*: hH <- traverse unconstrained (tHash :*: hdL)
        hash <- mzipWithMRep (hashF s) hH tH
        _ <- mzipWithMRep (\i j -> constraint (($ i) - ($ j))) hash y
        return (hH :*: tH)

-- | TODO: Is there really a nicer way to handle empty lists?
--
head ::
  (Symbolic c, SymbolicData x) =>
  (Context x ~ c, Support x ~ Proxy c, Representable (Payload x)) =>
  List c x -> x
head = fst . uncons

tail ::
  (Symbolic c, SymbolicData x) =>
  (Context x ~ c, Support x ~ Proxy c, Representable (Payload x)) =>
  List c x -> List c x
tail = snd . uncons

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

singleton
    :: forall context x
    .  Symbolic context
    => SymbolicData x
    => Context x ~ context
    => Support x ~ Proxy context
    => x
    -> List context x
singleton x = x .: emptyList

(!!) :: List context x -> UInt n Auto context -> x
(!!) = undefined

concat :: List context (List context x) -> List context x
concat = undefined
