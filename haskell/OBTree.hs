import Data.Sequence

data OBTree k v = Leaf | Node k v (OBTree k v) (OBTree k v) deriving Show

insert :: Ord k => OBTree k v -> k -> v -> (OBTree k v)
insert Leaf k v = Node k v Leaf Leaf
insert (Node k1 v1 t1 t2) k v
  | k == k1 = Node k1 v t1 t2
  | k < k1  = Node k1 v1 (insert t1 k v) t2
  | k1 < k  = Node k1 v1 t1 (insert t2 k v)

listToTree :: Ord k => [(k,v)] -> OBTree k v
listToTree [] = Leaf
listToTree ((k,v):xs) = insert (listToTree xs) k v 

treeToList :: (OBTree k v) -> [(k,v)]
treeToList Leaf = []
treeToList (Node a b t1 t2) = (a,b):(treeToList t1 ++ treeToList t2)

tree1 :: OBTree Int String
tree1 = listToTree  [(1,"john"),(3,"paul"),(2,"matthew"),(5,"luc"),(0,"jesus"),
                    (-1,"edward"),(4,"george")]

tree2 = insert tree1 6 "thomas"

depthFirst :: (Show k, Show v)  => OBTree k v -> IO ()
depthFirst Leaf = return ()
depthFirst (Node k v t1 t2) = depthFirst t1 >> putStrLn (show (k,v)) >> depthFirst t2

depthFirstList :: OBTree k v -> [(k,v)]
depthFirstList Leaf = []
depthFirstList (Node k v t1 t2) = depthFirstList t1 ++ [(k,v)] ++ depthFirstList t2







