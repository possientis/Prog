{-# LANGUAGE FlexibleInstances, OverlappingInstances #-} 

import Data.List

class Foo a where
  foo :: a -> String

instance Foo a => Foo [a] where
  foo = concat . intersperse ", " . map foo

instance Foo Char where
 foo c = [c]

instance Foo String where
  foo = id

instance Foo Int where
  foo = show


main = do
  putStrLn (foo "hello world") -- will not compile without 'OverlappingInstances
  putStrLn (foo ['a','b','c'])
  putStrLn (foo ([0,1,2,3,4,5] :: [Int])) 
