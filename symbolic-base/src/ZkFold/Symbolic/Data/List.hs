{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.List where

import           Control.Monad                    (return)
import           Data.Distributive                (Distributive (..))
import           Data.Function                    (const)
import           Data.Functor                     (Functor)
import           Data.Functor.Rep                 (Representable, distributeRep, pureRep, tabulate)
import           Data.List.Infinite               (Infinite (..))
import           Data.Proxy                       (Proxy (..))
import           Data.Traversable                 (traverse)
import           Data.Tuple                       (snd)
import           GHC.Generics                     (Generic, Generic1, Par1 (..), (:*:) (..), (:.:) (..))
import           Prelude                          (fmap, fst, type (~), undefined, ($), (.), (<$>))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Functor.Rep     ()
import           ZkFold.Base.Data.HFunctor        (hmap)
import           ZkFold.Base.Data.List.Infinite   ()
import           ZkFold.Base.Data.Product         (fstP, sndP)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional (Conditional)
import           ZkFold.Symbolic.Data.Eq          (Eq)
import           ZkFold.Symbolic.Data.Input       (SymbolicInput)
import           ZkFold.Symbolic.Data.Payloaded   (Payloaded (Payloaded))
import           ZkFold.Symbolic.Data.UInt        (UInt)
import           ZkFold.Symbolic.MonadCircuit

data ListItem l p a = ListItem
  { tailHash    :: l a
  , headLayout  :: l a
  , headPayload :: p a
  }
  deriving (Functor, Generic1)

instance (Representable l, Representable p) => Distributive (ListItem l p) where
  distribute = distributeRep

instance (Representable l, Representable p) => Representable (ListItem l p)

data List c x = List
  { lHash    :: c (Layout x)
  , lSize    :: c Par1
  , lWitness :: Payloaded (Infinite :.: ListItem (Layout x) (Payload x)) c
  }
  deriving (Generic)

instance (SymbolicData x, c ~ Context x) => SymbolicData (List c x)
-- | TODO: Maybe some 'isValid' check for Lists?..
instance (SymbolicInput x, c ~ Context x) => SymbolicInput (List c x)
instance (SymbolicInput x, c ~ Context x) => Conditional (Bool c) (List c x)
instance (SymbolicInput x, c ~ Context x) => Eq (List c x)

-- | TODO: A proof-of-concept where hash == id.
-- Replace id with a proper hash if we need lists to be cryptographically secure.
--
emptyList
    :: forall context x
    .  SymbolicData x
    => Context x ~ context
    => List context x
emptyList = List (embed $ pureRep zero) (embed $ Par1 zero) $ Payloaded $ tabulate (const zero)

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
    .  SymbolicOutput x
    => Context x ~ context
    => x
    -> List context x
    -> List context x
x .: List{..} = List incSum incSize ((witnessF lHash, witnessF (arithmetize x Proxy), payload x Proxy)<:<lWitness)
    where
        (a, b, c) <:< Payloaded (Comp1 l) = Payloaded $ Comp1 (ListItem a b c :< l)

        xRepr :: context (Layout x)
        xRepr = arithmetize x (Proxy @context)

        incSize :: context Par1
        incSize = fromCircuitF lSize (\(Par1 s) -> Par1 <$> newAssigned (\p -> p s + one))

        incSum :: context (Layout x)
        incSum = fromCircuit3F lHash xRepr incSize $
            \vHash vRepr (Par1 s) -> mzipWithMRep (hashFun s) vHash vRepr

hashFun :: MonadCircuit i a w m => i -> i -> i -> m i
hashFun s h t = newAssigned (($ h) + ($ t) * ($ s))

uncons ::
  forall c x.
  SymbolicOutput x =>
  Context x ~ c =>
  List c x -> (x, List c x)
uncons List{..} = case lWitness of
  Payloaded (Comp1 (ListItem {..} :< tWitness)) ->
    ( restore $ const (hmap fstP preimage, headPayload)
    , List (hmap sndP preimage) decSize $ Payloaded (Comp1 tWitness))
    where
      decSize = fromCircuitF lSize $ \(Par1 i) ->
        Par1 <$> newAssigned (($ i) - one)

      preimage :: c (Layout x :*: Layout x)
      preimage = fromCircuit2F lSize lHash $ \(Par1 s) y -> do
        tH :*: hH <- traverse unconstrained (tailHash :*: headLayout)
        hash <- mzipWithMRep (hashFun s) hH tH
        _ <- mzipWithMRep (\i j -> constraint (($ i) - ($ j))) hash y
        return (hH :*: tH)

-- | TODO: Is there really a nicer way to handle empty lists?
--
head ::
  SymbolicOutput x =>
  Context x ~ c =>
  List c x -> x
head = fst . uncons

tail ::
  SymbolicOutput x =>
  Context x ~ c =>
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
    .  SymbolicOutput x
    => Context x ~ context
    => x
    -> List context x
singleton x = x .: emptyList

(!!) :: List context x -> UInt n Auto context -> x
(!!) = undefined

concat :: List context (List context x) -> List context x
concat = undefined
