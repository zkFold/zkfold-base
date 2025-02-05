{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE TypeOperators             #-}


module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Lookup where

import           Control.DeepSeq
import           Data.ByteString (ByteString)
import           Data.Maybe      (fromJust)
import           Data.Set
import           Data.Typeable
import           GHC.Base
import           GHC.Generics    (Generic, Par1, (:*:))
import           Prelude         (Show)


data LookupType a = forall f. (Functor f, Typeable f) => LookupType { lTable :: LookupTable a f }

deriving instance (Show a) => Show (LookupType a)
-- deriving instance (ToJSON a) => ToJSON (LookupType a)
-- deriving instance (ToJSONKey a) => ToJSONKey (LookupType a)

tryEq :: (Typeable f, Typeable g, Typeable a, Eq a) => LookupTable a f -> LookupTable a g -> Bool
tryEq a b = (typeOf a == typeOf b) && (a == fromJust (cast b))

instance (Eq a, Typeable a) => Eq (LookupType a) where
  (==) :: LookupType a -> LookupType a -> Bool
  (==) (LookupType lt1) (LookupType lt2) = tryEq lt1 lt2

tryCompare :: (Ord a, Typeable a, Typeable b) => a -> b -> Ordering
tryCompare a b = if typeOf a == typeOf b then compare a (fromJust (cast b)) else EQ

instance (Typeable a, Ord a) => Ord (LookupType a) where
  compare :: LookupType a -> LookupType a -> Ordering
  compare (LookupType lt1) (LookupType lt2) = tryCompare lt1 lt2

-- | @LookupTable a f@ is a type of compact lookup table descriptions using ideas from relational algebra.
-- @a@ is a base field type, @f@ is a functor such that @f a@ is a type whose subset this lookup table describes.
data LookupTable a f where
  -- | @Ranges@ describes a set of disjoint intervals on the base field.
  Ranges :: Set (a, a) -> LookupTable a Par1
  -- | @Product t u@ is a cartesian product of tables @t@ and @u@.
  Product :: LookupTable a f -> LookupTable a g -> LookupTable a (f :*: g)
  -- | @Plot f x@ is a plot of a function @f@ with @x@ as a domain.
  Plot :: FunctionId (f a -> g a) -> LookupTable a f -> LookupTable a (f :*: g)


newtype FunctionId f = FunctionId { funcHash :: ByteString }
  deriving (Eq, Ord, Show, Generic)

deriving instance (Eq a) => Eq (LookupTable a f)
deriving instance (Ord a) => Ord (LookupTable a f)
deriving instance (Show a) => Show (LookupTable a f)
-- deriving instance (ToJSON a) => ToJSON (LookupTable a f)
-- deriving instance (ToJSONKey a) => ToJSONKey (LookupTable a f)
--
instance NFData (LookupType a) where
  rnf (LookupType _) = undefined


isRange :: LookupType a -> Bool
isRange (LookupType l) = case l of
  Ranges _ -> True
  _        -> False

fromRange :: LookupType a -> Set (a, a)
fromRange (LookupType (Ranges a)) = a
fromRange _                       = error "it's not Range lookup"
