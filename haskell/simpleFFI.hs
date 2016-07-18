{-# LANGUAGE ForeignFunctionInterface #-}

-- gcc -c test.c
-- ghc simpleFFI.hs test.o
-- ghci simpleFFI.hs test.o
import Foreign
import Foreign.C.Types
-- import Foreign.C.String
-- import Foreign.Ptr
-- import Foreign.Marshal.Array

foreign import ccall "math.h sin" 
  c_sin :: CDouble -> CDouble

fastsin :: Double -> Double
fastsin x = realToFrac (c_sin (realToFrac x))


main = mapM_ (print . fastfunc) [0..10]

foreign import ccall "test.h myfunc"
  c_myfunc :: CDouble -> CDouble

fastfunc :: Double -> Double
fastfunc x = realToFrac (c_myfunc (realToFrac x))


