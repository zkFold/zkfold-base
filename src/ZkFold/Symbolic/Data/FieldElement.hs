{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.FieldElement where

import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..))
import qualified ZkFold.Symbolic.Compiler.Arithmetizable             as A
import           ZkFold.Symbolic.Interpreter                         (Interpreter (..))

-- | A class for serializing data types into containers holding finite field elements.
-- Type `b` is the container type.
-- Type `x` represents the data type.
class FieldElementData b x where

    type TypeSize b x :: Natural

    -- | Returns the representation of `x` as a container of finite field elements.
    toFieldElements :: x -> b (TypeSize b x)

    -- | Restores `x` from its representation as a container of finite field elements.
    fromFieldElements :: b (TypeSize b x) -> x

-- | Returns the number of finite field elements needed to describe `x`.
typeSize :: forall b x . KnownNat (TypeSize b x) => Natural
typeSize = value @(TypeSize b x)

instance Arithmetic a => FieldElementData (Interpreter a) () where
    type TypeSize (Interpreter a) () = 0

    toFieldElements () = Interpreter V.empty

    fromFieldElements _ = ()

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
