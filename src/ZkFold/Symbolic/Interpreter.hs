module ZkFold.Symbolic.Interpreter where

import           Control.DeepSeq         (NFData)
import           Data.Eq                 (Eq)
import           GHC.Generics            (Generic)
import           Text.Show               (Show)

import           ZkFold.Base.Data.Vector (Vector)
import           ZkFold.Symbolic.Class

newtype Interpreter a n = Interpreter { runInterpreter :: Vector n a }
    deriving (Eq, Show, Generic, NFData)

instance Symbolic (Interpreter a) where
    type BaseField (Interpreter a) = a
