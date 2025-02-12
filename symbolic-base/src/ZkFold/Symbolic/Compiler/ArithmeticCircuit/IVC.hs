{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.IVC where

import           Control.Applicative                                 (Applicative (..))
import           Control.Monad.State                                 (State)
import           Data.ByteString                                     (ByteString)
import           Data.Either                                         (Either (..))
import           Data.Foldable                                       (Foldable (..))
import           Data.Function                                       ((.))
import           Data.Functor                                        (Functor (..))
import           Data.Functor.Rep                                    (Rep)
import           Data.List.Infinite                                  (Infinite)
import           Data.Map.Lazy                                       (Map)
import qualified Data.Map.Lazy                                       as M
import           Data.Maybe                                          (fromJust)
import           Data.Monoid                                         (Monoid (..))
import           Data.Semigroup                                      (Semigroup (..))
import           Data.Tuple                                          (uncurry)
import           GHC.Generics                                        (Par1 (..), U1 (..), (:*:) (..), (:.:))
import           Prelude                                             (error)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative                    (HApplicative (..))
import           ZkFold.Base.Data.ByteString                         (Binary, fromByteString)
import           ZkFold.Symbolic.Class                               (Symbolic (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Var      (SysVar, Var)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness  (WitnessF)
import           ZkFold.Symbolic.Data.Bool                           (Bool)
import           ZkFold.Symbolic.Data.Class                          (LayoutFunctor, PayloadFunctor)
import           ZkFold.Symbolic.Data.Conditional                    (Conditional (..))
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement (..))
import           ZkFold.Symbolic.Data.Ord                            (Ord (..))

data RangeEntry a v = RangeEntry
  { reUpperBound :: a
  , reRangedVars :: [v]
  }

type PCWitness v a p i = WitnessF a (Either (Rep p) (SysVar i v))

data PrimitiveCircuit v a p i n o = PrimitiveCircuit
  { pcSystem  :: [Constraint a i v]
  , pcRange   :: [RangeEntry a (SysVar i v)]
  , pcWitness :: Map v (PCWitness v a p i)
  , pcPayload :: n (PCWitness v a p i)
  , pcOutput  :: o (Var a i v)
  }

data RecursiveCircuit v a p i n o =
  forall sp si it.
  RecursiveCircuit
  { rcStep :: PrimitiveCircuit v a sp (si :*: it) sp si
  , rcBoot :: PrimitiveCircuit v a (p :*: sp) (i :*: si)
                  (n :*: sp :*: (Infinite :.: it))
                  (o :*: si :*: Par1)
  }

data FoldingCircuit a ext =
  forall p l i.
  FoldingCircuit
  { fcLayoutStep  :: ArithmeticCircuit a p (l :*: i) l
  , fcWitnessStep :: p (CircuitWitness a p (l :*: i))
  , fcSeedPayload :: p (WitnessField ext)
  , fcSeedLayout  :: ext l
  , fcStream      :: Infinite (i (WitnessField ext))
  , fcCount       :: FieldElement ext
  , fcOutPayload  :: Map ByteString (ByteString -> Rep p)
  , fcOutLayout   :: Map ByteString (ByteString -> Rep l)
  }

fromFold ::
  ByteString -> CircuitFold a (ACVar a i) (CircuitWitness a p i) ->
  FoldingCircuit a (ArithmeticCircuit a p i)
fromFold fldID CircuitFold {..} = FoldingCircuit
  { fcLayoutStep = foldStep
  , fcWitnessStep = foldStepP
  , fcSeedPayload = foldSeedP
  , fcSeedLayout = emptyCircuit { acOutput = foldSeed }
  , fcStream = foldStream
  , fcCount = FieldElement emptyCircuit { acOutput = Par1 foldCount }
  , fcOutPayload = M.singleton fldID (fromJust . fromByteString)
  , fcOutLayout = M.singleton fldID (fromJust . fromByteString)
  }

instance Symbolic c => Semigroup (FoldingCircuit a c) where
  FoldingCircuit _ _ sp sl s k op ol <> FoldingCircuit _ _ tp tl t l pp pl =
    FoldingCircuit
      { fcLayoutStep = error "TODO"
      , fcWitnessStep = error "TODO"
      , fcSeedPayload = sp :*: tp
      , fcSeedLayout = hpair sl tl
      , fcStream = liftA2 (:*:) s t
      , fcCount = bool k l (k < l :: Bool c)
      , fcOutPayload = fmap (Left .) op <> fmap (Right .) pp
      , fcOutLayout = fmap (Left .) ol <> fmap (Right .) pl
      }

instance Symbolic c => Monoid (FoldingCircuit a c) where
  mempty = FoldingCircuit
    { fcLayoutStep = emptyCircuit
    , fcWitnessStep = U1
    , fcSeedPayload = U1
    , fcSeedLayout = hunit
    , fcStream = pure U1
    , fcCount = zero
    , fcOutPayload = M.empty
    , fcOutLayout = M.empty
    }

recursiveCircuit ::
  ArithmeticCircuit a p i o -> State [v] (RecursiveCircuit v a p i U1 o)
recursiveCircuit = error "TODO"

foldingCircuit ::
  (Arithmetic a, Binary a, LayoutFunctor i, PayloadFunctor p) =>
  Map ByteString (CircuitFold a (ACVar a i) (CircuitWitness a p i)) ->
  FoldingCircuit a (ArithmeticCircuit a p i)
foldingCircuit = foldMap (uncurry fromFold) . M.assocs
