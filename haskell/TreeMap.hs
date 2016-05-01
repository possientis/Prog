data Tree a = Node (Tree a) (Tree a) | Leaf a deriving Show

treeLengths (Leaf s) = Leaf (length s)
treeLengths (Node l r) = Node (treeLengths l) (treeLengths r)


treeMap :: (a -> b) -> Tree a -> Tree b
treeMap f (Leaf a)    = Leaf (f a)
treeMap f (Node l r)  = Node (treeMap f l) (treeMap f r)

tree = Node (Leaf "foo")(Node (Leaf "x") (Leaf "quux"))

test1 = treeLengths tree      -- Node (Leaf 3) (Node (Leaf 1) (Leaf 4))
test2 = treeMap length tree   -- Node (Leaf 3) (Node (Leaf 1) (Leaf 4))

-- Haskell provides a typeclass 'Functor' which generalizes treeMap

{-
 - class Functor f where
 -   fmap :: (a -> b) -> f a -> f b 
-}

-- note that an instance of Functor is not a type of kind '*'
-- it is a generic type (parameterized, dependent type ?) of kind '* -> *'
-- In Coq, it would be of type Type -> Type ('Type' some fixed universe) 
-- Hence an instance of class Functor is a map: Type -> Type
-- If we mentally think of Type as the 'category' of types, where
-- arrows are maps a -> b, then an instance of class 'Functor' must be
-- a map beteen the category of types to itself
--
-- Now fmap is the part of the functor which provides the transformation
-- of morphisms. i.e. suppose h : a -> b is a morphism between 
-- objects a and b of the category Type. If f is a functor Type -> Type
-- (kind * -> *), then we have the objects f a and f b, and we should also 
-- have a morphism f h: f a -> f b. This is what the fmap function does, 
-- hence its type: (a -> b) -> f a -> f b. 

-- Now Tree is a map : Type -> Type, hence a candidate for being turned 
-- intro a functor. We already have the 'lifting' map TreeMap.
-- Note however, that defining fmap :: (a -> b) -> f a -> f b may be 
-- enough to create an instance of Haskell class 'Functor', but if we
-- want the notion to coincide with the categorical notion, we shall
-- need to ensure that fmap f1.f2 = (fmap f1).(fmap f2)

instance Functor Tree where
  fmap = treeMap

test3 = fmap length tree  -- Node (Leaf 3) (Node (Leaf 1) (Leaf 4))



