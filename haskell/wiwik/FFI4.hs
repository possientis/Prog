{-# LANGUAGE ForeignFunctionInterface #-}
-- ghc FFI4.hs FFI_example.c -o a.out; ./a.out

import Foreign
import System.IO
import Foreign.C.Types (CInt(..))

foreign import ccall "wrapper"
    makeFunPtr :: (CInt -> IO ()) -> IO (FunPtr (CInt -> IO ()))

foreign import ccall "FFI_example.c invoke"
    invoke :: FunPtr (CInt -> IO ()) -> IO ()


fn :: CInt -> IO ()
fn n = do
    putStrLn "Hello from Haskell, here's the number passed between runtimes:"
    print n
    hFlush stdout

main :: IO ()
main = do
    fptr <- makeFunPtr fn
    invoke fptr

{-
 - Linking a.out ...
 - inside of C, now we'll call Haskell
 - Hello from Haskell, here's the number passed between runtimes:
 - 42
 - back in side of C again
-}
