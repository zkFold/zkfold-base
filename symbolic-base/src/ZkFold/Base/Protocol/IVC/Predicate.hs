module ZkFold.Base.Protocol.IVC.Predicate where

import           Prelude                                         hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.FieldElement               (FieldElement (..))

predicate :: (forall ctx' . Symbolic ctx' => Vector nx (FieldElement ctx') -> Vector nu (FieldElement ctx') -> Vector nx (FieldElement ctx'))
    -> (forall ctx' . Symbolic ctx' => Vector nx (FieldElement ctx') -> Vector nx (FieldElement ctx') -> Vector nu (FieldElement ctx') -> Vector nx (FieldElement ctx'))
predicate f _ = f