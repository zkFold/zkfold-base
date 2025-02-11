module ZkFold.Base.Protocol.IVC.CycleFold.Utils where

import           GHC.Generics (Par1 (..))

type ForeignField = Par1 -- functor for transforming into "native context" (see NativeContext.hs)

type PrimaryField = Par1 -- Fq
type PrimaryGroup = Par1 -- Point with Fp coordinates

type SecondaryField = Par1 -- Fp
type SecondaryGroup = Par1 -- Point with Fq coordinates
