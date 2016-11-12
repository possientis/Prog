data List a = Nil | Cons a (List a)

instance (Eq a) => Eq (List a) where
  Nil         == Nil          = True
  Nil         == (Cons _ _)   = False
  (Cons _ _)  == Nil          = False
  (Cons x xs) == (Cons y ys)  = (x == y) && (xs == ys)  -- should be tail recursive


instance Monad List where
  return a        = Cons a Nil
  Nil       >>= f = Nil
  Cons x xs >>= f = append (f x) (xs >>= f)

instance (Show a) => Show (List a) where
  show x = show $ toList x

append :: List a -> List a -> List a
append Nil ys         = ys
append (Cons x xs) ys = Cons x (append xs ys)

toList :: List a -> [a]
toList Nil = []
toList (Cons x xs) = x : toList xs

fromList :: [a] -> List a
fromList [] = Nil
fromList (x:xs) = Cons x (fromList xs)

sqr :: Int -> Int
sqr n  = n * n

test0 = fromList [2,0,5,7]

test1 :: List Int
test1 = do
  x <- test0
  return $ sqr x

test2 :: List Int 
test2 = test0 >>= return . sqr


