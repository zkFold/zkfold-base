module Examples.FFA
  ( exampleFFAadd337
  , exampleFFAadd097
  , exampleFFAmul337
  , exampleFFAmul097) where

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Class            (Symbolic)
import           ZkFold.Symbolic.Data.FFA         (FFA)

type Prime256_1 = 28948022309329048855892746252171976963363056481941560715954676764349967630337
type Prime256_2 = 28948022309329048855892746252171976963363056481941647379679742748393362948097

exampleFFAadd337 :: Symbolic c => FFA Prime256_1 c -> FFA Prime256_1 c -> FFA Prime256_1 c
exampleFFAadd337 = exampleFFAadd

exampleFFAadd097 :: Symbolic c => FFA Prime256_2 c -> FFA Prime256_2 c -> FFA Prime256_2 c
exampleFFAadd097 = exampleFFAadd

exampleFFAmul337 :: Symbolic c => FFA Prime256_1 c -> FFA Prime256_1 c -> FFA Prime256_1 c
exampleFFAmul337 = exampleFFAmul

exampleFFAmul097 :: Symbolic c => FFA Prime256_2 c -> FFA Prime256_2 c -> FFA Prime256_2 c
exampleFFAmul097 = exampleFFAmul

exampleFFAadd :: forall p c. (Symbolic c, KnownNat p) => FFA p c -> FFA p c -> FFA p c
exampleFFAadd = (+)

exampleFFAmul :: forall p c. (Symbolic c, KnownNat p) => FFA p c -> FFA p c -> FFA p c
exampleFFAmul = (*)
