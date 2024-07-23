{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FieldElement where

import           GHC.Generics                                        (Par1 (..))
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Bool, Eq, Num (..), Ord, drop, length,
                                                                      product, splitAt, sum, take, (!!), (^))
import qualified Prelude                                             as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit (..), mapOutputs, withOutputs)
import qualified ZkFold.Symbolic.Compiler.Arithmetizable             as A
import           ZkFold.Symbolic.Data.Bool                           (Bool)
import           ZkFold.Symbolic.Data.Eq                             (Eq)
import           ZkFold.Symbolic.Interpreter                         (Interpreter (..), mapInterpreter)

newtype FieldElement c = FieldElement { fromFieldElement :: c Par1 }

deriving instance Show (c Par1) => Show (FieldElement c)

deriving instance Haskell.Eq (c Par1) => Haskell.Eq (FieldElement c)

instance A.Arithmetic a => A.SymbolicData a (FieldElement (ArithmeticCircuit a)) where
    type TypeSize a (FieldElement (ArithmeticCircuit a)) = 1
    pieces (FieldElement x) = mapOutputs (V.singleton . unPar1) x
    restore c = FieldElement . withOutputs c . Par1 . V.item

instance A.Arithmetic a => A.Arithmetizable a (FieldElement (ArithmeticCircuit a)) where
    type InputSize a (FieldElement (ArithmeticCircuit a)) = 0
    type OutputSize a (FieldElement (ArithmeticCircuit a)) = 1
    arithmetize (FieldElement x) _ = mapOutputs (V.singleton . unPar1) x

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

-- | A class for serializing data types into containers holding finite field elements.
-- Type `c` is the container type.
-- Type `x` represents the data type.
class FieldElementData c x where

    type TypeSize c x :: Natural

    -- | Returns the representation of `x` as a container of finite field elements.
    toFieldElements :: x -> c (Vector (TypeSize c x))

    -- | Restores `x` from its representation as a container of finite field elements.
    fromFieldElements :: c (Vector (TypeSize c x)) -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall c x . KnownNat (TypeSize c x) => Natural
typeSize = value @(TypeSize c x)

instance FieldElementData (Interpreter a) () where
    type TypeSize (Interpreter a) () = 0

    toFieldElements () = Interpreter V.empty

    fromFieldElements _ = ()

instance FieldElementData (Interpreter a) (FieldElement (Interpreter a)) where
    type TypeSize (Interpreter a) (FieldElement (Interpreter a)) = 1

    toFieldElements (FieldElement x) = mapInterpreter (V.singleton . unPar1) x

    fromFieldElements = FieldElement . mapInterpreter (Par1 . V.item)

instance
    ( FieldElementData (Interpreter a) x
    , FieldElementData (Interpreter a) y
    , m ~ TypeSize (Interpreter a) x
    , KnownNat m
    ) => FieldElementData (Interpreter a) (x, y) where

    type TypeSize (Interpreter a) (x, y) =
        TypeSize (Interpreter a) x + TypeSize (Interpreter a) y

    toFieldElements (a, b) = Interpreter $
        runInterpreter (toFieldElements a)
        `V.append` runInterpreter (toFieldElements b)

    fromFieldElements (Interpreter v) =
        (fromFieldElements (Interpreter v1), fromFieldElements (Interpreter v2))
        where
            (v1, v2) = V.splitAt @m v

instance
    ( FieldElementData (Interpreter a) x
    , FieldElementData (Interpreter a) y
    , FieldElementData (Interpreter a) z
    , m ~ TypeSize (Interpreter a) x
    , n ~ TypeSize (Interpreter a) y
    , KnownNat m
    , KnownNat n
    ) => FieldElementData (Interpreter a) (x, y, z) where

    type TypeSize (Interpreter a) (x, y, z) =
        TypeSize (Interpreter a) x + TypeSize (Interpreter a) y + TypeSize (Interpreter a) z

    toFieldElements (a, b, c) = Interpreter $
        runInterpreter (toFieldElements a)
        `V.append` runInterpreter (toFieldElements b)
        `V.append` runInterpreter (toFieldElements c)

    fromFieldElements (Interpreter v) =
        (fromFieldElements (Interpreter v1)
        , fromFieldElements (Interpreter v2)
        , fromFieldElements (Interpreter v3))
        where
            (v1, v2, v3) = V.splitAt3 @m @n v

instance
    ( FieldElementData (Interpreter a) x
    , m ~ TypeSize (Interpreter a) x
    , KnownNat m
    ) => FieldElementData (Interpreter a) (Vector n x) where

    type TypeSize (Interpreter a) (Vector n x) = n * TypeSize (Interpreter a) x

    toFieldElements xs = Interpreter . V.concat $ runInterpreter . toFieldElements <$> xs

    fromFieldElements (Interpreter v) = fromFieldElements . Interpreter <$> V.chunks v

instance A.SymbolicData a x => FieldElementData (ArithmeticCircuit a) x where
    type TypeSize (ArithmeticCircuit a) x = A.TypeSize a x

    toFieldElements = A.pieces

    fromFieldElements ArithmeticCircuit {..} = A.restore acCircuit acOutput
