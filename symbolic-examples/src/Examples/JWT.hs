module Examples.JWT (exampleJWTSerialisation) where

import           Control.DeepSeq                    (NFData)
import           GHC.Generics                       (Par1)

import           ZkFold.Base.Data.Vector            (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.JWT           (ClientSecret, TokenHeader, TokenPayload, secretBits, toAsciiBits)
import           ZkFold.Symbolic.Data.VarByteString (VarByteString)

--exampleJWTSerialisation :: (Symbolic c, NFData (c (Vector 1))) => ClientSecret c ->  VarByteString 10328 c
--exampleJWTSerialisation = secretBits

--exampleJWTSerialisation :: (Symbolic c, NFData (c (Vector 1))) => TokenPayload c -> VarByteString 9456 c
exampleJWTSerialisation
    :: Symbolic c
    => NFData (c (Vector 1))
    => NFData (c (Vector 8))
    => NFData (c (Vector 648))
    => NFData (c (Vector 864))
    => NFData (c (Vector 9456))
    => NFData (c (Vector 10328))
    => NFData (c Par1)
    => ClientSecret c -> VarByteString 10328 c
exampleJWTSerialisation = secretBits
