import qualified Queue 
import qualified Stack

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

-- the natural way to carry out depth first search with recursion
-- This is not tail recursive to the stack will grow
depthFirst' :: (Show k, Show v)  => OBTree k v -> IO ()
depthFirst' Leaf = return ()
depthFirst' (Node k v t1 t2) = depthFirst t1 >> putStrLn (show (k,v)) >> depthFirst t2

depthFirstList' :: OBTree k v -> [(k,v)]
depthFirstList' Leaf = []
depthFirstList' (Node k v t1 t2) = depthFirstList t1 ++ [(k,v)] ++ depthFirstList t2

-- breast first search requires a Queue
-- Queue can become as large as there are elements (or leaf) in the tree O(n)
breastFirst :: (Show k, Show v) => OBTree k v -> IO ()
breastFirst tree = processQueue (Queue.push Queue.empty tree) where
  processQueue :: (Show k, Show v) => Queue.Queue (OBTree k v) -> IO ()
  processQueue q =  if Queue.isEmpty q then return () else let top = Queue.peek q in
                    case top of
                      Just Leaf -> processQueue (Queue.pop q)
                      Just (Node k v t1 t2) -> do
                        putStrLn (show (k,v))
                        processQueue (Queue.push (Queue.push (Queue.pop q) t1) t2)

-- in fact, depth first search can be carried out just like breast first search,
-- replacing the queue by a stack. However, needs to push right subtree first 
-- here the stack is explicit. The function is tail recursive so the semantic stack
-- does not grow, however the explicit stack does.
-- not that Stack size does not grow beyond depth of tree O(log n)
-- So DFS is more efficient than BFS from a space point of view
-- WARNING: actually not so clear in what order (LeftTree, NodeValue, RightTree)
-- things should be ordered, regardless of whether we use a stack of queue.
-- question of all the various ways a binary tree can be processed 
depthFirst :: (Show k, Show v) => OBTree k v -> IO ()
depthFirst tree = processStack (Stack.push Stack.empty tree) where
  processStack :: (Show k, Show v) => Stack.Stack (OBTree k v) -> IO ()
  processStack q =  if Stack.isEmpty q then return () else let top = Stack.peek q in
                    case top of
                      Just Leaf -> processStack (Stack.pop q)
                      Just (Node k v t1 t2) -> do
                        putStrLn (show (k,v))
                        processStack (Stack.push (Stack.push (Stack.pop q) t2) t1)

breastFirstList :: OBTree k v -> [(k,v)]
breastFirstList tree = processQueueList (Queue.push Queue.empty tree) where
  processQueueList :: Queue.Queue (OBTree k v) -> [(k,v)]
  processQueueList q =  if Queue.isEmpty q then [] else let top = Queue.peek q in
                    case top of
                      Just Leaf -> processQueueList (Queue.pop q)
                      Just (Node k v t1 t2) ->
                        (k,v):processQueueList (Queue.push (Queue.push (Queue.pop q) t1) t2)

-- replace queue by stack and change order in which you push subtrees
depthFirstList :: OBTree k v -> [(k,v)]
depthFirstList tree = processStackList (Stack.push Stack.empty tree) where
  processStackList :: Stack.Stack (OBTree k v) -> [(k,v)]
  processStackList q =  if Stack.isEmpty q then [] else let top = Stack.peek q in
                    case top of
                      Just Leaf -> processStackList (Stack.pop q)
                      Just (Node k v t1 t2) ->
                        (k,v):processStackList (Stack.push (Stack.push (Stack.pop q) t2) t1)

