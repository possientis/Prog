import Control.Monad
import System.Directory
import Data.List
import System.IO



data NestedList a = Nil | (NestedList a) :||: (NestedList a) | a :|: (NestedList a)

x = (1:|:(2:|:Nil)):||:(4:|:(Nil:||:(((5:|:Nil):||:(10:|:Nil)):||:Nil)))

instance Show a => Show (NestedList a) where
  show Nil = "nil"
  show (xs:||:Nil) = "[" ++ (show xs) ++ "]"
  show (xs:||:ys) = "[" ++ (show xs) ++ " " ++ zs where (z:zs) = show ys
  show (x:|:Nil) = "[" ++ (show x) ++ "]"
  show (x:|:xs) = "[" ++ (show x) ++ " " ++ zs where (z:zs) = show xs

count :: NestedList a -> Int
count Nil = 0
count (x:|:xs) = 1 + count xs
count (xs:||:ys) = count xs + count ys

flatten :: NestedList a -> [a]
flatten Nil = []
flatten (xs :||: ys) = flatten xs ++ flatten ys
flatten (x :|: xs ) = x:flatten xs
