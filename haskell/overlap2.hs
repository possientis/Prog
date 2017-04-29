{-# LANGUAGE FlexibleInstances #-}
 
class M m where
  foo :: m v -> Int
  bar :: m v -> String

instance (M m) => Eq (m v) where
  (==) x y = (foo x) == (foo y) 

instance (M m) => Show (m v) where
  show = bar

data A v = A v
instance M A where
  foo x = 1
  bar x = "bar"

x = A 2
y = A 3


main = do
  print x
  print y
  print (x == y)
--  print [x]
  if [x] == [y] then return () else return ()


