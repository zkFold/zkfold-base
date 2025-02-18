{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Algorithms.Hash.MiMC where

import           Data.Foldable                                  (toList)
import           Data.Functor.Rep                               (pureRep)
import           Data.List.NonEmpty                             (NonEmpty ((:|)), nonEmpty)
import           Data.Proxy                                     (Proxy (..))
import           GHC.Generics                                   ((:*:) (..))
import           Numeric.Natural                                (Natural)
import           Prelude                                        hiding (Eq (..), Num (..), any, length, not, (!!), (/),
                                                                 (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative               (hpair)
import           ZkFold.Base.Data.HFunctor                      (hmap)
import           ZkFold.Base.Data.Package                       (unpacked)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.MonadCircuit                   (MonadCircuit (newAssigned))

-- | MiMC-2n/n (Feistel) hash function.
-- See https://eprint.iacr.org/2016/492.pdf, page 5
mimcHash2 :: forall c x a.(FromConstant a x, c ~ Context x, Symbolic c, SymbolicData x) => [a] -> a -> x -> x -> x
mimcHash2 (map fromConstant -> xs) (fromConstant @a @x -> k) =
    case nonEmpty (reverse xs) of
      Just cs -> go cs
      Nothing -> error "mimcHash: empty list"
    where
      go :: NonEmpty x -> x -> x -> x
      go (c :| cs) xL xR =
        let
          t5 = restore $ \s ->
            (fromCircuit3F
                (hpair (arithmetize xL s) (arithmetize k s)) (arithmetize c s) (arithmetize xR s)
                (\ (a1 :*: a2) a3 r
                    -> do s3 <- liftMR3 sum3 a1 a2 a3
                          p5 <- fmapMRep pow5 s3
                          mzipWithMRep sum2 p5 r )
            , pureRep zero)
        in case nonEmpty cs of
            Just cs' -> go cs' t5 xL
            Nothing  -> t5

sum2 :: MonadCircuit i a w m => i -> i -> m i
sum2 h t = newAssigned (($ h) + ($ t))

sum3 :: MonadCircuit i a w m => i -> i -> i -> m i
sum3 s h t = newAssigned (($ h) + ($ t) + ($ s))

pow5 :: MonadCircuit i a w m => i -> m i
pow5 s = newAssigned (($ s) ^ (5 :: Natural))

mimcHashN :: (FromConstant a x, Ring x, SymbolicData x) => [a] -> a -> [x] -> x
mimcHashN xs k = go
  where
    go zs = case zs of
      []          -> mimcHash2 xs k zero zero
      [z]         -> mimcHash2 xs k zero z
      [zL, zR]    -> mimcHash2 xs k zL zR
      (zL:zR:zs') -> go (mimcHash2 xs k zL zR : zs')

hash :: forall context x a .
    ( SymbolicOutput x
    , BaseField context ~ a
    , Context x ~ context
    ) => x -> FieldElement context
hash = mimcHashN mimcConstants (zero :: a) . fmap FieldElement . unpacked . hmap toList . flip arithmetize Proxy
