{-# LANGUAGE Arrows #-}

import Control.Arrow

idA :: a -> a
idA = proc a -> returnA -< a

plusOne:: Int -> Int
plusOne = proc a -> returnA -< (a+1)
plusTwo = proc a -> plusOne -< (a+1)

plusTwo' =
  proc a -> do
    b <- plusOne -< a
    plusOne -< b

plusFive = 
  proc a -> do  b <- plusOne -< a
                c <- plusOne -< b
                d <- plusOne -< c
                e <- plusOne -< d
                plusOne -< e
