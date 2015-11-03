data Tree a = EmptyTree | Node a (Tree a) (Tree a) deriving (Show, Read, Eq)

newNode :: a -> Tree a
newNode x = Node x EmptyTree EmptyTree

treeInsert :: (Ord a) => a -> Tree a -> Tree a
treeInsert x EmptyTree = newNode x
treeInsert x (Node y left right)
  | x == y = Node x left right
  | x < y  = Node y (treeInsert x left) right
  | y < x  = Node y left (treeInsert x right)

treeElem :: (Ord a) => a -> Tree a -> Bool
treeElem x EmptyTree = False
treeElem x (Node y left right)
  | x == y = True
  | x < y = treeElem x left
  | y < x = treeElem x right

nums = [8,6,4,1,7,3,5]
numsTree = foldr treeInsert EmptyTree nums

treeToList :: Tree a -> [a]
treeToList EmptyTree = []
treeToList (Node x left right) = (treeToList left) ++ [x] ++ (treeToList right)

