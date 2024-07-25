module ZkFold.Symbolic.Class where

import           Data.Kind                        (Type)

import           ZkFold.Base.Control.HApplicative (HApplicative)
import           ZkFold.Base.Data.Package         (Package)

class (HApplicative c, Package c) => Symbolic c where
    type BaseField c :: Type
