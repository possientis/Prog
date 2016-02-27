data Set = Empty | Singleton Set | Union Set Set | Set Int

inc :: Set -> Set
inc x = Union x (Singleton x)

zero  = Empty
one   = inc zero
two   = inc one
three = inc two
four  = inc three 

instance Show Set where
  show Empty          = "0"
  show (Set n)        = (show n)
  show (Singleton x)  = "{"++(show x)++"}"
  show (Union Empty y) = show y
  show (Union x Empty) = show x
  show (Union (Set n) (Set m)) = (show (max n m))
  show (Union (Set n) x)  = "{"++(show n)++","++(drop 1 (show x))
  show (Union x (Set n))  = (init (show x))++","++(show n)++"}"
  show (Union x y)    = (init (show x))++","++(drop 1 (show y))

set :: Int -> Set
set n = Set n

instance Eq Set where
  (==) x y = (subset x y) && (subset y x)

instance Ord Set where
  (<=) x y = subset x y

subset :: Set -> Set -> Bool
subset Empty _         = True
subset (Singleton x) y = belong x y
subset (Union x y) z   = (subset x z) && (subset y z)
subset (Set n) (Set m) = n <= m
subset (Set n)  y      = and [belong (set x) y| x <- [0..(n-1)]] 

belong :: Set -> Set -> Bool
belong x Empty         = False
belong x (Singleton y) = (x == y)
belong x (Union y z)   = (belong x y) || (belong x z)
belong (Set x) (Set y) = x < y
belong x (Set n)       = or [x == (set y) | y <- [0..(n-1)]]

fromList :: [Int] -> Set
fromList [] = Set 0
fromList (x:xs) = Union (Set x) (fromList xs)

-- This is a mess
