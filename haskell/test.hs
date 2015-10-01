import Data.List
import Data.Function


search :: (Eq a) => [a] -> [a] -> Bool
search needle haystack =
  let nlen = length needle
  in foldl (\acc x -> if take nlen x == needle then True else acc )
  False (tails haystack)

average :: (Fractional a) => [a] -> a
average xs = sum xs / genericLength xs
