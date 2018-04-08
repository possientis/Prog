{-# LANGUAGE TypeFamilies #-}

import Data.Vector
import Data.Primitive.ByteArray

data family Array a -- compact storage of elements of type a
data instance Array Bool = MkArrayBool ByteArray
data instance Array Int  = MkArrayInt (Vector Int)
