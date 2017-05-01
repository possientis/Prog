{-# LANGUAGE FlexibleInstances #-}
 
class M m where
  foo :: m v -> Int
  bar :: m v -> String

data A v = A v
instance M A where
  foo x = 1
  bar x = "bar"

x = wrap $ A 2
y = wrap $ A 3

newtype WrappedM m a = WrappedM { unwrap :: m a }

wrap :: m a -> WrappedM m a
wrap = WrappedM

instance (M m) => Show (WrappedM m v) where
  show = bar . unwrap

instance (M m) => Eq (WrappedM m v) where
  (==) x y = (foo $ unwrap x) == (foo $ unwrap y)


main = do
  print x 
  print y
  print (x == y)
  print [x]
  if [x] == [y] then return () else return ()


