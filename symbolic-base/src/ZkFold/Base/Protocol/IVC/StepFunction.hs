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

type StepFunction i p = forall ctx . Symbolic ctx => i (FieldElement ctx) -> p (FieldElement ctx) -> i (FieldElement ctx)
