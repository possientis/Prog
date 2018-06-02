{-# Language DeriveFoldable #-}
{-# Language GeneralizedNewtypeDeriving #-}

import Data.Monoid ((<>), mempty)
import Data.Foldable (toList, length)

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


data Inorder a  
    = ILeaf
    | INode (Inorder a) a (Inorder a)   -- same as Tree
    deriving Foldable

inorder :: Tree a -> Inorder a
inorder Leaf          = ILeaf
inorder (Node l v r)  = INode (inorder l) v (inorder r)

myInorder = inorder myTree


data Preorder a 
    = PrLeaf
    | PrNode a (Preorder a) (Preorder a)
    deriving Foldable 

preorder :: Tree a -> Preorder a
preorder Leaf         = PrLeaf
preorder (Node l v r) = PrNode v (preorder l) (preorder r)

myPreorder = preorder myTree


data Postorder a 
    = PoLeaf
    | PoNode (Postorder a) (Postorder a) a
    deriving Foldable

postorder :: Tree a -> Postorder a
postorder Leaf         = PoLeaf
postorder (Node l v r) = PoNode (postorder l) (postorder r) v

myPostorder = postorder myTree

newtype Plus = Plus Int deriving (Show, Num)


instance Monoid Plus where
    mempty = 0
    mappend = (+)

main :: IO ()
main = do
    print $ foldMap (\x -> [x]) myTree 
    print $ foldMap (\x -> [x]) myInorder
    print $ foldMap (\x -> [x]) myPreorder
    print $ foldMap (\x -> [x]) myPostorder
    print $ foldr (:) [] myTree
    print $ foldr (:) [] myInorder
    print $ foldr (:) [] myPreorder
    print $ foldr (:) [] myPostorder
    print $ toList myTree
    print $ toList myInorder
    print $ toList myPreorder
    print $ toList myPostorder
    print $ foldMap (\x -> Plus 1) myTree
    print $ foldMap (\x -> Plus 1) myInorder
    print $ foldMap (\x -> Plus 1) myPreorder
    print $ foldMap (\x -> Plus 1) myPostorder
    print $ length myTree
    print $ length myInorder
    print $ length myPreorder
    print $ length myPostorder


                




