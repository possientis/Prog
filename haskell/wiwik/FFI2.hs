{-# LANGUAGE ForeignFunctionInterface #-}
-- gcc -c FFI_example.c; ghc FFI2.hs FFI_example.o -o a.out; ./a.out

import Foreign.Ptr
import Foreign.C.Types

import qualified Data.Vector.Storable as V
import qualified Data.Vector.Storable.Mutable as VM

foreign import ccall safe "qsort" qsort   -- string is C name
    :: Ptr a -> CInt -> CInt -> IO ()


main :: IO ()
main = do
    let vs = V.fromList ([1,3,5,2,1,2,5,9,6] :: [CInt])
    v <- V.thaw vs
    VM.unsafeWith v $ \ptr -> do
        qsort ptr 0 9
    out <- V.freeze v
    print out



