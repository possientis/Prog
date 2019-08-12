data Tree a = Empty | Node (Tree a) a (Tree a)

%name Tree t, t1, t2

insert : (Ord a) => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x t@(Node tl y tr) = 
  case compare x y of
       LT => Node (insert x tl) y tr
       EQ => t
       GT => Node tl y (insert x tr)


listToTree : (Ord a) => List a -> Tree a
listToTree []        = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : Tree a -> List a
treeToList Empty          = []
treeToList (Node tl x tr) = treeToList tl ++ (x :: treeToList tr)



main : IO ()
main = do
  printLn $ treeToList $ listToTree [0,3,1,8,5,4,6,7,9,2]


