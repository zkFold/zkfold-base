module Examples.JWT (exampleJWTSerialisation) where

import           Control.DeepSeq                    (NFData)
import           GHC.Generics                       (Par1)

import           ZkFold.Base.Data.Vector            (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.ByteString    (ByteString, shiftBitsL)
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.Data.JWT           (ClientSecret, SecretBits, secretBits)
import           ZkFold.Symbolic.Data.VarByteString (VarByteString, append, shiftL)

exampleJWTSerialisation
    :: Symbolic c
    => SecretBits c
    => NFData (c Par1)
    => ClientSecret c -> VarByteString 10328 c
exampleJWTSerialisation = secretBits
