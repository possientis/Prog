data List a = Nil | Cons a (List a)

instance (Eq a) => Eq (List a) where
  Nil         == Nil          = True
  Nil         == (Cons _ _)   = False
  (Cons _ _)  == Nil          = False
  (Cons x xs) == (Cons y ys)  = (x == y) && (xs == ys)  -- should be tail recursive
