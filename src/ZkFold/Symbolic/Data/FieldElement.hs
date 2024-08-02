{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FieldElement where

import           GHC.Generics                                        (Par1 (..))
import           Prelude                                             hiding (Bool, Eq, Num (..), Ord, drop, length,
                                                                      product, splitAt, sum, take, (!!), (^))
import qualified Prelude                                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.HFunctor                           (hmap, HFunctor)
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Symbolic.Data.Bool                           (Bool)
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Eq                             (Eq)

newtype FieldElement c = FieldElement { fromFieldElement :: c Par1 }

deriving instance Show (c Par1) => Show (FieldElement c)

deriving instance Haskell.Eq (c Par1) => Haskell.Eq (FieldElement c)

instance HFunctor c => SymbolicData c (FieldElement c) where
    type Support c (FieldElement c) = ()
    type TypeSize c (FieldElement c) = 1

    pieces (FieldElement x) _ = hmap (V.singleton . unPar1) x
    restore = FieldElement . hmap (Par1 . V.item) . ($ ())

deriving newtype instance FromConstant k (c Par1) => FromConstant k (FieldElement c)

instance (MultiplicativeSemigroup p, Exponent (c Par1) p) => Exponent (FieldElement c) p where
    FieldElement x ^ a = FieldElement (x ^ a)

deriving newtype instance (MultiplicativeMonoid k, Scale k (c Par1)) => Scale k (FieldElement c)

deriving newtype instance MultiplicativeSemigroup (c Par1) => MultiplicativeSemigroup (FieldElement c)

deriving newtype instance MultiplicativeMonoid (c Par1) => MultiplicativeMonoid (FieldElement c)

deriving newtype instance AdditiveSemigroup (c Par1) => AdditiveSemigroup (FieldElement c)

deriving newtype instance AdditiveMonoid (c Par1) => AdditiveMonoid (FieldElement c)

deriving newtype instance AdditiveGroup (c Par1) => AdditiveGroup (FieldElement c)

deriving newtype instance Semiring (c Par1) => Semiring (FieldElement c)

deriving newtype instance Ring (c Par1) => Ring (FieldElement c)

deriving newtype instance Field (c Par1) => Field (FieldElement c)

deriving newtype instance Eq (Bool c) (c Par1) => Eq (Bool c) (FieldElement c)
