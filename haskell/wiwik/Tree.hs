import Data.Tree

{-
 -      A
 -     / \
 -    B   C
 -       / \
 -      D   E
 -
 -}

tree :: Tree String
tree = Node "A" [Node "B" [],Node "C" [Node "D" [], Node "E" []]]


postorder :: Tree a -> [a]
postorder (Node a ts) = elts ++ [a] where
    elts = concat $ map postorder ts
-- ["B","D","E","C","A"]

preorder  :: Tree a -> [a]
preorder (Node a ts) = a : elts where
    elts = concat $ map preorder ts 
-- ["A","B","C","D","E"]


ex1 :: String
ex1 = drawTree tree
{-
A
|
+- B
|
`- C
   |
   +- D
   |
   `- E
-}

ex2 :: String
ex2 = drawForest (subForest tree)

{-
B

C
|
+- D
|
`- E

-}


ex3 :: [String]
ex3 = flatten tree  -- ["A","B","C","D","E"]

ex4 :: [[String]]
ex4 = levels tree   -- [["A"],["B","C"],["D","E"]]

main :: IO ()
main = do
    print $ postorder tree  
    print $ preorder tree   
    putStrLn ex1
    putStrLn ex2
    print ex3
    print ex4

