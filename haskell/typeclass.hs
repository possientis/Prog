import Data.List

class Equatable a where
  isEqual :: a -> a -> Bool
  isDifferent :: a-> a -> Bool
  isDifferent x y = not (isEqual x y)

class Comparable a where
  compare :: a -> a -> Int

instance Equatable Integer where
  isEqual x y  = x == y

instance Equatable Char where
 isEqual x y  = x == y

instance (Equatable a, Equatable b) => Equatable (a,b) where
 isEqual (u,v) (x,y) = (isEqual u x) && (isEqual v y)

instance Equatable a => Equatable [a] where
  isEqual [] []      = True -- will fail without indentation
  isEqual [] (x:xs)  = False
  isEqual (x:xs) []  = False
  isEqual (x:xs) (y:ys) = (isEqual x y) && (isEqual xs ys)

data Equator a = MakeEquator (a -> a -> Bool)

eq :: Equator a -> a -> a -> Bool
eq (MakeEquator f) = f

isElem :: Equator a -> a -> [a] -> Bool
isElem d x ys = or [eq d x y | y <- ys]

data List a = Nil | Cons a (List a)

toList :: List a -> [a]
toList Nil = []
toList (Cons x ys) = x:toList ys

instance Show a => Show (List a) where
  show xs = Prelude.show (toList xs)







