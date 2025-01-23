{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Data.Morph where

import           Data.Function              (const, ($), (.))
import           Data.Proxy                 (Proxy (..))
import           Data.Type.Equality         (type (~))

import           ZkFold.Symbolic.Class      (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Class (SymbolicData (..), SymbolicOutput)
import           ZkFold.Symbolic.Fold       (SymbolicFold)

type Replica c t u =
  ( SymbolicOutput u, Context u ~ c
  , Layout u ~ Layout t, Payload u ~ Payload t)

data MorphTo c input output =
  forall i o. (Replica c input i, Replica c output o) => Morph (i -> o)

(@) ::
  (Replica c input i, Replica c output o) =>
  MorphTo c input output -> i -> o
Morph f @ x =
  let y = f . restore $ const (arithmetize x Proxy, payload x Proxy)
   in restore $ const (arithmetize y Proxy, payload y Proxy)

type MorphFrom ctx input output =
  forall c.
  (SymbolicFold c, BaseField c ~ BaseField ctx) =>
  MorphTo c input output
