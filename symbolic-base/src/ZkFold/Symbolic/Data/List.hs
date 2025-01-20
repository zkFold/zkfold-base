{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module ZkFold.Symbolic.Data.List where

import           Control.Monad                     (return)
import           Data.Distributive                 (Distributive (..))
import           Data.Function                     (const)
import           Data.Functor                      (Functor (..))
import           Data.Functor.Rep                  (Representable (..), pureRep, tabulate)
import           Data.List.Infinite                (Infinite (..))
import           Data.Proxy                        (Proxy (..))
import           Data.Traversable                  (Traversable, traverse)
import           Data.Tuple                        (snd)
import           GHC.Generics                      (Generic, Generic1, Par1 (..), (:*:) (..), (:.:) (..))
import           Prelude                           (fst, type (~), undefined, ($), (.), (<$>))
import qualified Prelude                           as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative  (HApplicative (..))
import           ZkFold.Base.Data.Orphans          ()
import           ZkFold.Base.Data.HFunctor         (hmap)
import           ZkFold.Base.Data.List.Infinite    ()
import           ZkFold.Base.Data.Product          (fstP, sndP)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool         (Bool (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (..))
import           ZkFold.Symbolic.Data.Input        (SymbolicInput)
import           ZkFold.Symbolic.Data.Payloaded    (Payloaded (Payloaded, runPayloaded))
import           ZkFold.Symbolic.Data.UInt         (UInt)
import           ZkFold.Symbolic.Fold
import           ZkFold.Symbolic.MonadCircuit

data ListItem l p a = ListItem
  { tailHash    :: l a
  , headLayout  :: l a
  , headPayload :: p a
  }
  deriving (Functor, Generic1, Representable)

instance (Distributive l, Distributive p) => Distributive (ListItem l p) where
  distribute f = ListItem
    { tailHash = distribute (tailHash <$> f)
    , headLayout = distribute (headLayout <$> f)
    , headPayload = distribute (headPayload <$> f)
    }

data List c x = List
  { lHash    :: c (Layout x)
  , lSize    :: c Par1
  , lWitness :: Payloaded (Infinite :.: ListItem (Layout x) (Payload x)) c
  }
  deriving (Generic)

instance (SymbolicData x, c ~ Context x) => SymbolicData (List c x)
-- | TODO: Maybe some 'isValid' check for Lists?..
instance (SymbolicInput x, c ~ Context x) => SymbolicInput (List c x)

-- | TODO: A proof-of-concept where hash == id.
-- Replace id with a proper hash if we need lists to be cryptographically secure.
--
emptyList
    :: forall context x
    .  SymbolicData x
    => Context x ~ context
    => List context x
emptyList = List (embed $ pureRep zero) (fromFieldElement zero) $ Payloaded $ tabulate (const zero)

null
    :: forall context x
    .  Symbolic context
    => List context x
    -> Bool context
null List{..} = FieldElement lSize == zero

infixr 5 .:
(.:)
    :: forall context x
    .  SymbolicOutput x
    => Context x ~ context
    => x
    -> List context x
    -> List context x
x .: List{..} = List incSum incSize (Payloaded incWitness)
    where
      (incSum, incSize, incWitness) =
        appImpl
          lHash
          lSize
          (runPayloaded lWitness)
          (arithmetize x Proxy)
          (payload x Proxy)

appImpl ::
  (Symbolic c, Representable l, Traversable l) =>
  c l -> c Par1 -> (Infinite :.: ListItem l p) (WitnessField c) ->
  c l -> p (WitnessField c) ->
  (c l, c Par1, (Infinite :.: ListItem l p) (WitnessField c))
appImpl lHash lSize (Comp1 lWitness) headL headP =
  (incHash, incSize, Comp1 (incItem :< lWitness))
  where
    incHash = fromCircuit3F lHash headL incSize \vHash vRepr (Par1 s) ->
      mzipWithMRep (hashFun s) vHash vRepr
    incSize = fromFieldElement (FieldElement lSize + one)
    incItem = ListItem (witnessF lHash) (witnessF headL) headP

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
      decSize = fromFieldElement (FieldElement lSize - one)

      preimage :: c (Layout x :*: Layout x)
      preimage = fromCircuit2F decSize lHash $ \(Par1 s) y -> do
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

reverse ::
  forall x c.
  (SymbolicData x, Context x ~ c, SymbolicFold c) =>
  List c x -> List c x
reverse List {..} =
  let (l, p) =
        sfoldl
        (\hs w it ->
          let (ih, is, iw) = appImpl
                    (hmap fstP hs)
                    (hmap sndP hs)
                    w
                    (hmap fstP it)
                    (witnessF $ hmap sndP it)
           in (hpair ih is, iw)
        )
        (embed $ pureRep zero)
        (pureRep zero)
        lHash
        (fmap (\ListItem {..} -> headLayout :*: headPayload) . unComp1 $ runPayloaded lWitness)
        lSize
   in List
      { lHash = hmap fstP l
      , lSize = hmap sndP l
      , lWitness = Payloaded p
      }

last :: List c x -> x
last = Haskell.error "TODO" -- head . reverse

init :: List c x -> List c x
init = Haskell.error "TODO" -- reverse . tail . reverse

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
