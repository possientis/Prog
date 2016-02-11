data BookInfo = Book {

  indentifier :: Int, 
  title       :: String, 
  authors     :: [String] 

} deriving Show



book1 = Book 0 "abce" ["john", "luc"]

-- generic algebraic data type parameterized with type variables
-- are these so called 'dependent types' of coq?
data Map k v = Map [(k,v)]
map' = Map [("a",4), ("b",7), ("c", 9)]
search (Map xs) k = snd (head [(x,y) | (x,y) <- xs, x == k])







