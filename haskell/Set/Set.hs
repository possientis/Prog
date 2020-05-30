module  Set
    (   Set     (..)
    ,   toList
    ,   fromList
    ,   zero, one, two, three, four, five
    ,   main
    )   where

import Test.QuickCheck

data Set = Nil | Cons Set Set
    deriving (Eq, Show)

-- lexicographic order based on syntax. Not set inclusion !!
instance Ord Set where
    (<=) Nil _   = True
    (<=) _   Nil = False
    (<=) (Cons x xs) (Cons y ys) = 
        (x /= y) && (x <= y) || (x == y) && (xs <= ys)

instance Arbitrary Set where
    arbitrary = chooseSet 10

chooseSet :: Int -> Gen Set
chooseSet n = do
    k <- choose (0,n)
    if k == 0
        then return Nil
        else do
            x  <- chooseSet (k - 1)
            xs <- chooseSet (n - 1)
            return $ Cons x xs

main :: IO ()
main = do
    sample (arbitrary :: Gen Set)


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
