import Data.List
import Data.Function
import Data.Char
import qualified Data.Map as Map


search :: (Eq a) => [a] -> [a] -> Bool
search needle haystack =
  let nlen = length needle
  in foldl (\acc x -> if take nlen x == needle then True else acc )
  False (tails haystack)

average :: (Fractional a) => [a] -> a
average xs = sum xs / genericLength xs

-- instance of naive impl of dict
dict = [("if",0),("else",1),("then",2),("elseif",3)]

findKey :: (Eq k) => k -> [(k,v)] -> [(k,v)]
findKey k = filter (\(k',_) -> (k' == k))

findKey' key= foldr (\(k,v) acc -> if k == key then Just v else acc) Nothing

dict' = Map.fromList dict

fromList' :: (Ord k) => [(k,v)] -> Map.Map k v
fromList' = foldr (\(k,v) acc -> Map.insert k v acc) Map.empty



