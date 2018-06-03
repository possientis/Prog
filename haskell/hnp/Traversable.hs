import Data.Traversable
import Data.Monoid ((<>), mempty)

data Tree a = Leaf | Node (Tree a) a (Tree a)

myTree :: Tree Char
myTree = Node (Node Leaf 'a' Leaf) 'b' (Node Leaf 'c' Leaf)

instance Functor Tree where
    fmap f Leaf = Leaf
    fmap f (Node l v r) = Node (fmap f l) (f v) (fmap f r)


instance Foldable Tree where
    foldMap f Leaf = mempty
    foldMap f (Node l v r) = foldMap f l <> f v <> foldMap f r


instance Traversable Tree where
    traverse f Leaf = pure Leaf
    traverse f (Node l v r) = Node <$> (traverse f l) <*> (f v) <*> (traverse f r)


main :: IO ()
main = do
    _ <- traverse print myTree
    return ()


