module  Set
    (   Set     (..)
    ,   toList
    ,   fromList
    ,   zero, one, two, three, four, five
    )   where

data Set = Nil | Cons Set Set
    deriving Eq

-- lexicographic order based on syntax. Not set inclusion !!
instance Ord Set where
    (<=) Nil _   = True
    (<=) _   Nil = False
    (<=) (Cons x xs) (Cons y ys) = 
        (x /= y) && (x <= y) || (x == y) && (xs <= ys)

zero :: Set
zero = Nil

one :: Set
one = Cons zero zero

two :: Set
two = Cons one one

three :: Set
three = Cons two two

four :: Set
four = Cons three three

five :: Set
five = Cons four four

fromList :: [Set] -> Set
fromList [] = Nil
fromList (x : xs) = Cons x (fromList xs) 

toList :: Set -> [Set]
toList Nil = []
toList (Cons x xs) = x : (toList xs)


