{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Bool (
    BoolType(..),
    Bool(..),
    all,
    all1,
    any
) where

import           GHC.Generics                                              (Par1 (..))
import           Prelude                                                   hiding (Bool, Num (..), all, any, not, (&&),
                                                                            (/), (||))
import qualified Prelude                                                   as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Base.Algebra.Basic.Number                          (KnownNat)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Arithmetic, ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (MonadBlueprint (newAssigned, runCircuit),
                                                                            circuit)
import           ZkFold.Symbolic.Interpreter                               (Interpreter (..))

class BoolType b where
    true  :: b

    false :: b

    not   :: b -> b

    infixr 3 &&
    (&&)  :: b -> b -> b

    infixr 2 ||
    (||)  :: b -> b -> b

    xor  :: b -> b -> b

instance BoolType Haskell.Bool where
    true  = True

    false = False

    not   = Haskell.not

    (&&)  = (Haskell.&&)

    (||)  = (Haskell.||)

    xor = xor

-- TODO (Issue #18): hide this constructor
newtype Bool c = Bool (c Par1)

deriving instance Eq (c Par1) => Eq (Bool c)

instance KnownNat p => Show (Bool (Interpreter (Zp p))) where
    show (fromBool -> x) = if x == one then "True" else "False"

instance Arithmetic a => BoolType (Bool (ArithmeticCircuit a)) where
    true = Bool $ circuit $ newAssigned one

    false = Bool $ circuit $ newAssigned zero

    not (Bool b) = Bool $ circuit $ do
      v <- unPar1 <$> runCircuit b
      newAssigned (one - ($ v))

    Bool b1 && Bool b2 = Bool $ circuit $ do
      v1 <- unPar1 <$> runCircuit b1
      v2 <- unPar1 <$> runCircuit b2
      newAssigned (($ v1) * ($ v2))

    Bool b1 || Bool b2 = Bool $ circuit $ do
      v1 <- unPar1 <$> runCircuit b1
      v2 <- unPar1 <$> runCircuit b2
      newAssigned (\x -> let x1 = x v1; x2 = x v2 in x1 + x2 - x1 * x2)

    Bool b1 `xor` Bool b2 = Bool $ circuit $ do
      v1 <- unPar1 <$> runCircuit b1
      v2 <- unPar1 <$> runCircuit b2
      newAssigned (\x -> let x1 = x v1; x2 = x v2 in x1 + x2 - (one + one) * x1 * x2)

fromBool :: Bool (Interpreter a) -> a
fromBool (Bool (Interpreter (Par1 b))) = b

toBool :: a -> Bool (Interpreter a)
toBool = Bool . Interpreter . Par1

instance Arithmetic a => BoolType (Bool (Interpreter a)) where
    true = Bool $ Interpreter $ Par1 one

    false = Bool $ Interpreter $ Par1 zero

    not (fromBool -> b) = Bool $ Interpreter $ Par1 $ one - b

    (fromBool -> b1) && (fromBool -> b2) = toBool $ b1 * b2

    (fromBool -> b1) || (fromBool -> b2) = toBool $ b1 + b2 - b1 * b2

    (fromBool -> b1) `xor` (fromBool -> b2) = toBool $ b1 + b2 - (one + one) * b1 * b2

all :: (BoolType b, Foldable t) => (x -> b) -> t x -> b
all f = foldr ((&&) . f) true

all1 :: (BoolType b, Functor t, Foldable t) => (x -> b) -> t x -> b
all1 f = foldr1 (&&) . fmap f

any :: (BoolType b, Foldable t) => (x -> b) -> t x -> b
any f = foldr ((||) . f) false
