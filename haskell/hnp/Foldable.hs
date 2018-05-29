import Data.Monoid

data Tree a = Leaf | Node (Tree a) a (Tree a)


instance Functor Tree where
    fmap f Leaf = Leaf
    fmap f (Node l v r) = Node (fmap f l) (f v) (fmap f r)

instance Applicative Tree where
    pure v = Node Leaf v Leaf
    Leaf <*> _      = Leaf
    _    <*> Leaf   = Leaf
    (Node lf f rf) <*> (Node l v r) = Node (lf <*> l) (f v) (rf <*> r) 


instance Foldable Tree where
    foldMap f Leaf = mempty
    foldMap f (Node l v r) = foldMap f l <> f v <> foldMap f r


myTree :: Tree Char
myTree = Node (Node Leaf 'a' Leaf) 'b' (Node Leaf 'c' Leaf)


main :: IO ()
main = do
    print $ foldMap (\x -> [x]) myTree 
