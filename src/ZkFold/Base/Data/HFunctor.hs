module ZkFold.Base.Data.HFunctor where

class HFunctor c where
  hmap :: (forall a. f a -> g a) -> c f -> c g
