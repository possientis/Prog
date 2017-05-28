{-# LANGUAGE Arrows #-}

import Control.Arrow
import Control.Category

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

-- wrapping a -> b so as to avoid clash with Control.Arrow
newtype Morphism a b = Morphism (a -> b)  

instance Category Morphism where
  id = Morphism (\x -> x)
  (Morphism g) . (Morphism f) = Morphism (\x -> g (f x))

instance Arrow Morphism where
  arr                           = Morphism
  (Morphism f) *** (Morphism g) = Morphism (\(x,y) -> (f x, g y))

addA :: Arrow a => a b Int -> a b Int -> a b Int
addA f g = proc x -> do
  y <- f -< x
  z <- g -< x
  returnA -< y + z

addA' :: Arrow a => a b Int -> a b Int -> a b Int
addA' f g = arr (\x -> (x,x)) >>>
  first f >>> arr (\(y,x) -> (x,y)) >>>
  first g >>> arr (\(x,y) -> x + y)

addA'' :: Arrow a => a b Int -> a b Int -> a b Int
addA'' f g = f &&& g >>> arr (\(x,y) -> x + y)
