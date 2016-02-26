data Set = Empty | Singleton Set | Union Set Set

inc :: Set -> Set
inc x = Union x (Singleton x)

zero  = Empty
one   = inc zero
two   = inc one
three = inc two
four  = inc three 

instance Show Set where
  show Empty          = "0"
  show (Singleton x)  = "{"++(show x)++"}"
  show (Union Empty y) = show y
  show (Union x Empty) = show x
  show (Union x y)    = (init (show x))++","++(drop 1 (show y))

toSet :: Int -> Set
toSet 0 = Empty
toSet n = inc (toSet (n - 1))

toInt :: Set -> Maybe Int
toInt Empty             = Just 0
toInt (Singleton Empty) = Just 1

isSucc :: Set -> Bool
isSucc Empty = False


