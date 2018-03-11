{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}

import GHC.Exts

ex1 :: Bool
ex1 = I# (gtChar# a# b#) == 1 where
    !(C# a#) = 'a'
    !(C# b#) = 'b'


ex2 :: Int 
ex2 = I# (a# +# b#) where
    !(I# a#) = 1
    !(I# b#) = 2


ex3 :: Int
ex3 = I# (1# +# 2# *# 3# +# 4#)


ex4 :: (Int,Int)
ex4 = (I# (dataToTag# False), I# (dataToTag# True))


plusInt :: Int -> Int -> Int
plusInt (I# x) (I# y) = I# (x +# y)

main :: IO ()
main = do
    print ex1
    print ex2
    print ex3
    print ex4
    print $ plusInt 4 5
