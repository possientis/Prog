module Set (ISet, empty, set, inc, belong, singleton, union, subset, Set) where

class ISet a where
  empty     :: a
  singleton :: a -> a
  union     :: a -> a -> a
  belong    :: a -> a -> Bool
  subset    :: a -> a -> Bool
  -- successor
  inc       :: a -> a
  inc x                   = union x (singleton x)
  -- Embedding for natural numbers
  set       :: Int -> a
  set 0                   = empty
  set 1                   = singleton empty
  set x                   = inc (set (x - 1))


data Set = Empty | Singleton Set | Union Set Set

instance Show Set where
  show Empty            = "0"
  show (Singleton x)    = "{"++(show x)++"}"
  show (Union Empty y)  = show y
  show (Union x Empty)  = show x
  show (Union x y)      = (init (show x))++","++(drop 1 (show y))

instance Eq Set where
  (==) x y = (subset x y) && (subset y x)

instance Ord Set where
  (<=) x y = subset x y

instance ISet Set where
  empty                   = Empty
  singleton x             = Singleton x
  union x y               = Union x y
  subset Empty _          = True
  subset (Singleton x) y  = belong x y
  subset (Union x y) z    = (subset x z) && (subset y z)
  belong x Empty          = False
  belong x (Singleton y)  = (x == y)
  belong x (Union y z)    = (belong x y) || (belong x z)






