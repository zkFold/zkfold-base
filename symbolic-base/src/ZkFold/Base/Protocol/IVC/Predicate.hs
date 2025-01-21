{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Control.DeepSeq                       (NFData)
import           Data.Binary                           (Binary)
import           Data.Functor.Rep                      (Representable (..))
import           GHC.Generics                          (U1 (..), (:*:) (..))
import           Prelude                               hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Algebra.Basic.Class       (Scale, FromConstant, FiniteField)
import           ZkFold.Base.Data.Package              (packed, unpacked)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler              (ArithmeticCircuit, compileWith, guessOutput, hlmap)
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement (..))

type PredicateFunctionAssumptions a f =
    ( FiniteField f
    , FromConstant a f
    , Scale a f
    )

type PredicateFunction a i p = forall f . PredicateFunctionAssumptions a f => i f -> p f -> i f
type PredicateCircuit a i p  = ArithmeticCircuit a (i :*: p) i i

data Predicate a i p = Predicate
    { predicateFunction :: PredicateFunction a i p
    , predicateCircuit  :: PredicateCircuit a i p
    }

type FunctorAssumptions t =
    ( Representable t
    , Traversable t
    , NFData (Rep t)
    , Binary (Rep t)
    , Ord (Rep t)
    )

predicate :: forall a i p .
    ( Arithmetic a
    , Binary a
    , FunctorAssumptions i
    , FunctorAssumptions p
    ) => PredicateFunction a i p -> Predicate a i p
predicate predicateFunction =
    let
        func' :: forall ctx .
            ( Symbolic ctx
            , FromConstant a (BaseField ctx)
            , Scale a (BaseField ctx)
            ) => ctx i -> ctx p -> ctx i
        func' x' u' =
            let
                x = FieldElement <$> unpacked x'
                u = FieldElement <$> unpacked u'
            in
                packed . fmap fromFieldElement $ predicateFunction x u

        predicateCircuit :: PredicateCircuit a i p
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @a guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) func'
    in Predicate {..}
