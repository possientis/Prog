{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

{-# OPTIONS_GHC -O1 #-}

module Main (main) where

import GHC.Exts
import GHC.Base
import Foreign

data Size = Size 
    { ptrs  :: Int
    , nptrs :: Int
    , size  :: Int
    } deriving (Show)


unsafeSizeof :: a -> Size
unsafeSizeof a = 
    case unpackClosure# a of
        (# x, ptrs, nptrs #) ->
            let header  = sizeOf (undefined :: Int)
                ptr_c   = I# (sizeofArray# ptrs)
                nptr_c  = I# (sizeofByteArray# nptrs) `div` sizeOf (undefined :: Word)
                payload = I# (sizeofArray# ptrs +# sizeofByteArray# nptrs)
                size    = header + payload
            in Size ptr_c nptr_c size 

data A = A {-# UNPACK #-} !Int
data B = B Int


-- dataToTag# :: a -> Int#


a :: (Int, Int)
a = (I# (dataToTag# False), I# (dataToTag# True))


b :: (Int, Int, Int)
b = (I# (dataToTag# LT), I# (dataToTag# EQ), I# (dataToTag# GT))


c :: (Int, Int)
c = (I# (dataToTag# (Left 34)), I# (dataToTag# (Right 67)))


-- unpackCString# :: Addr# -> [Char]




main :: IO ()
main = do
    print (unsafeSizeof (A 42))
    print (unsafeSizeof (B 42))
    putStrLn $ "a = " ++ (show a)
    putStrLn $ "b = " ++ (show b)
    putStrLn $ "c = " ++ (show c)
    print (unpackCString# "Hello world"#)






