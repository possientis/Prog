listRemove item list = filter (\x -> x /= item) list

listMerge []    list2   = list2
listMerge list1 []      = list1
listMerge (x:xs)(y:ys)  = x:y:listMerge xs ys

data Set a = Set [a] deriving Show

emptySet                = Set []
fromList list           = Set list
isEmpty (Set xs)        = null xs
singleton x             = Set [x]
union (Set xs) (Set ys) = Set (listMerge xs ys) -- sets can be infinite
member x (Set xs)       = elem x xs              -- will fail for infinite set :(
remove x (Set xs)       = Set (listRemove x xs)
split (Set [])          = error "split: cannot be applied to empty set"
split (Set (x:xs))      = (x, remove x (Set xs)) 

subset :: (Eq a) => (Set a) -> (Set a) -> Bool
subset x y = if isEmpty x then True else 
  let 
    (item, rest) = split x 
  in
    member item y && subset rest y

instance (Eq a) => Eq (Set a) where
  (==) x y = (subset x y) && (subset y x)

instance (Eq a) => Ord (Set a) where
  (<=) x y = (subset x y)
  (>=) x y = (subset y x)
  (<)  x y = (x <= y) && (x /= y)
  (>)  x y = (y <= x) && (x /= y) 
   

int :: Int -> Set Int
int 0 = emptySet
int n = union (singleton (n - 1)) (int (n - 1))


