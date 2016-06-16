import qualified Data.Map as Map

list1 = [(1, "one"), (2, "two"), (3, "three"), (4, "four")]

map1 = Map.fromList list1

map2 = foldl (\map (k,v) -> Map.insert k v map) Map.empty list1

map3 =  Map.insert 2 "two" . 
        Map.insert 1 "one" . 
        Map.insert 4 "four" . 
        Map.insert 3 "three" $ Map.empty



