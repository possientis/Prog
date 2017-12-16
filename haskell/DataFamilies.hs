{-# LANGUAGE TypeFamilies #-}

import qualified Data.Vector.Unboxed as V

data family Array a
data instance Array Int         = IArray (V.Vector Int)
data instance Array Bool        = BArray (V.Vector Bool)
data instance Array (a,b)       = PArray (Array a) (Array b)
data instance Array (Maybe a)   = MArray (V.Vector Bool) (Array a)


-- TODO
