data OBTree k v = Leaf | Node k v (OBTree k v) (OBTree k v) 

insert :: Ord k => OBTree k v -> k -> v -> (OBTree k v)
insert Leaf k v = Node k v Leaf Leaf
insert (Node k1 v1 t1 t2) k v
  | k == k1 = Node k1 v t1 t2
  | k < k1  = Node k1 v1 (insert t1 k v) t2
  | k1 < k  = Node k1 v1 t1 (insert t2 k v)




