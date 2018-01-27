{-# LANGUAGE ForeignFunctionInterface #-}

module FFI3
    (   malloc
    ,   malloc'
    )
    where

import Foreign.Ptr
import Foreign.C.Types

foreign import ccall unsafe "malloc.h malloc"
    malloc :: CSize -> IO (Ptr a)

--Prepending the function name with a & allows us to create a reference to the
--function pointer itself.
foreign import ccall unsafe "malloc.h &malloc"
    malloc' :: FunPtr a
