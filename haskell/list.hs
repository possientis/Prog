import Control.Monad
import System.Directory
import Data.List
import System.IO

data List a = Nil | a :|: List a

append :: List a -> List a -> List a
append Nil ys = ys
append (x:|:xs) ys = x :|: (append xs ys)

-- List a can be viewed as a computation returning many values
instance Monad List where
--  return :: a -> List a
  return x = x :|: Nil
--  (>>=) :: (List a) -> (a -> List b) -> (List b)
  Nil >>= k       = Nil
  (x:|:xs) >>= k  =  append (k x) (xs >>= k)

toBuiltInList :: List a -> [a]
toBuiltInList Nil = []
toBuiltInList (x:|:xs) = x:toBuiltInList xs

instance Show a => Show (List a) where
  show xs = show (toBuiltInList xs)

toList :: [a] -> List a
toList [] = Nil
toList (x:xs) = x:|:toList xs



