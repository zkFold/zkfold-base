module ZkFold.Symbolic.Interpreter (Interpreter (..)) where

import           Control.DeepSeq                  (NFData)
import           Data.Eq                          (Eq)
import           Data.Function                    (($))
import           Data.Functor                     ((<$>))
import           GHC.Generics                     (Generic)
import           Text.Show                        (Show)

import           ZkFold.Base.Control.HApplicative
import           ZkFold.Base.Data.HFunctor
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Class

newtype Interpreter a f = Interpreter { runInterpreter :: f a }
    deriving (Eq, Show, Generic, NFData)

instance HFunctor (Interpreter a) where
  hmap f (Interpreter x) = Interpreter (f x)

instance HApplicative (Interpreter a) where
  hpure = Interpreter
  hliftA2 f (Interpreter x) (Interpreter y) = Interpreter (f x y)

instance Package (Interpreter a) where
  unpackWith f (Interpreter x) = Interpreter <$> f x
  packWith f g = Interpreter $ f (runInterpreter <$> g)

instance Arithmetic a => Symbolic (Interpreter a) where
  type BaseField (Interpreter a) = a
  symbolicF (Interpreter x) f _ = Interpreter (f x)
