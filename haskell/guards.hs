odds :: [Integer] -> [Integer]
odds [] = []
odds (x:xs) 
  | odd x     = x:odds xs
  | otherwise = odds xs


data Tree a = Empty | Node a (Tree a) (Tree a)

tree1 = Node 3 (Node 1 Empty Empty) Empty
tree2 = Node 3 (Node 1 Empty Empty) Empty

instance (Eq a) =>  Eq (Tree a) where
  (==) Empty          Empty         = True
  (==) Empty          (Node _ _ _)  = False
  (==) (Node _ _ _)   Empty         = False
  (==) (Node x t1 t2) (Node y s1 s2)
    | x == y                        = (t1 == s1) && (t2 == s2)
    | otherwise                     = False
