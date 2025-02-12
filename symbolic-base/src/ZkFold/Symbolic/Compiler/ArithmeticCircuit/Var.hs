{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Var where

import           Control.Applicative             ()
import           Control.DeepSeq                 (NFData)
import           Data.Aeson                      (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Binary                     (Binary)
import           Data.ByteString                 (ByteString)
import           Data.Functor.Rep                (Rep, Representable, index, tabulate)
import           GHC.Generics                    (Generic)
import           GHC.Show                        (Show)
import           Prelude                         (Eq, Ord)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString     ()

data NewVar
  = EqVar ByteString
  | FoldVar ByteString ByteString
  deriving
    ( Generic, Binary, FromJSON, FromJSONKey, ToJSON, ToJSONKey
    , Show, Eq, Ord, NFData)

data SysVar i n
  = InVar (Rep i)
  | NewVar n
  deriving (Generic)

imapSysVar ::
  (Representable i, Representable j) =>
  (forall x. j x -> i x) -> SysVar i n -> SysVar j n
imapSysVar f (InVar r)  = index (f (tabulate InVar)) r
imapSysVar _ (NewVar v) = NewVar v

deriving anyclass instance (Binary (Rep i), Binary n) => Binary (SysVar i n)
deriving anyclass instance (NFData (Rep i), NFData n) => NFData (SysVar i n)
deriving anyclass instance
  (FromJSON (Rep i), FromJSON n) => FromJSON (SysVar i n)
deriving anyclass instance
  (FromJSON (Rep i), FromJSON n, FromJSONKey n) => FromJSONKey (SysVar i n)
deriving anyclass instance (ToJSON (Rep i), ToJSON n) => ToJSON (SysVar i n)
deriving anyclass instance
  (ToJSON (Rep i), ToJSON n, ToJSONKey n) => ToJSONKey (SysVar i n)
deriving stock instance (Show (Rep i), Show n) => Show (SysVar i n)
deriving stock instance (Eq (Rep i), Eq n) => Eq (SysVar i n)
deriving stock instance (Ord (Rep i), Ord n) => Ord (SysVar i n)

data Var a i n
  = LinVar a (SysVar i n) a
  | ConstVar a
  deriving Generic

toVar :: Semiring a => SysVar i n -> Var a i n
toVar x = LinVar one x zero

imapVar ::
  (Representable i, Representable j) =>
  (forall x. j x -> i x) -> Var a i n -> Var a j n
imapVar f (LinVar k x b) = LinVar k (imapSysVar f x) b
imapVar _ (ConstVar c)   = ConstVar c

deriving anyclass instance
  (Binary (Rep i), Binary a, Binary n) => Binary (Var a i n)
deriving anyclass instance
  (FromJSON (Rep i), FromJSON a, FromJSON n) => FromJSON (Var a i n)
deriving anyclass instance
  (FromJSON (Rep i), FromJSON a, FromJSON n, FromJSONKey n) =>
  FromJSONKey (Var a i n)
deriving anyclass instance
  (ToJSON (Rep i), ToJSON a, ToJSON n, ToJSONKey n) => ToJSONKey (Var a i n)
deriving anyclass instance
  (ToJSON (Rep i), ToJSON a, ToJSON n) => ToJSON (Var a i n)
deriving stock instance (Show (Rep i), Show a, Show n) => Show (Var a i n)
deriving stock instance (Eq (Rep i), Eq a, Eq n) => Eq (Var a i n)
deriving stock instance (Ord (Rep i), Ord a, Ord n) => Ord (Var a i n)
deriving instance (NFData (Rep i), NFData a, NFData n) => NFData (Var a i n)
instance FromConstant a (Var a i n) where fromConstant = ConstVar
