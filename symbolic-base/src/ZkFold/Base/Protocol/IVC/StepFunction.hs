{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.StepFunction where

import           Control.DeepSeq                   (NFData)
import           Data.Binary                       (Binary)
import           Data.Functor.Rep                  (Representable (..))
import           Prelude                           hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (..))

type FunctorAssumptions f =
    ( Representable f
    , Traversable f
    , NFData (Rep f)
    , Binary (Rep f)
    , Ord (Rep f)
    )

type StepFunctionAssumptions a f ctx =
    ( Symbolic ctx
    , BaseField ctx ~ a
    , FieldElement ctx ~ f
    )

type StepFunction a i p = forall f ctx . StepFunctionAssumptions a f ctx
    => i f -> p f -> i f