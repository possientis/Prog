-- gcc -c FFI_example.c; ghc FFI.hs FFI_example.o -o a.out; ./a.out

{-# LANGUAGE ForeignFunctionInterface #-}

import Foreign.C.Types

foreign import ccall safe "example" example
    :: CInt -> CInt -> CInt


main :: IO ()
main = print (example 42 47)
