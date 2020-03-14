module  Set
    (   Set     (..)
    ,   main
    ,   zero
    ,   one
    ,   two
    ,   three
    ,   four
    ,   five
    ,   fromList
    ,   toList
    ,   incl
    ,   equal
    ,   normalize
    ,   leq
    ,   toInt
    )   where

import Test.Hspec

data Set = Nil | Cons Set Set
    deriving Eq

instance Show Set where
    show = setShow

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

incl :: Set -> Set -> Bool
incl Nil _  = True
incl (Cons x xs) ys = incl xs ys && any f (toList ys) where
    f :: Set -> Bool
    f y = incl x y && incl y x

equal :: Set -> Set -> Bool
equal x y = incl x y && incl y x

belong :: Set -> Set -> Bool
belong x y = incl (Cons x Nil) y

normalize :: Set -> Set
normalize Nil = Nil
normalize (Cons x xs)
    | belong x xs   = normalize xs
    | otherwise     = insert (normalize x) (normalize xs)


-- should be called on normalized arguments
leq :: Set -> Set -> Bool
leq Nil _   = True
leq _   Nil = False
leq (Cons x xs) (Cons y ys)
    =  (x /= y) && (leq x y)
    || (x == y) && (leq xs ys)

insert :: Set -> Set -> Set
insert x Nil = Cons x Nil
insert x (Cons y ys)
    | leq x y   = Cons y (insert x ys)
    | otherwise = Cons x (Cons y ys) 

toInt :: Set -> Maybe Int
toInt x = case normalize x of
    Nil -> Just 0
    (Cons y ys) -> 
        if y == ys 
            then case toInt y of
                Nothing -> Nothing
                Just n  -> Just (n + 1)
            else Nothing

setShow :: Set -> String
setShow x = case toInt x of
    Just n  -> show n
    Nothing -> "{" ++ (help $ toList (normalize x)) ++ "}"

help :: [Set] -> String
help [] = ""
help [x] = setShow x
help (x : xs) = setShow x ++ "," ++ help xs

main :: IO ()
main = hspec $ do
    it "Testing 0 <= 1 " $ incl zero one        `shouldBe` True
    it "Testing 1 <= 2 " $ incl one two         `shouldBe` True
    it "Testing 2 <= 3 " $ incl two three       `shouldBe` True
    it "Testing 3 <= 4 " $ incl three four      `shouldBe` True
    it "Testing 4 <= 5 " $ incl four five       `shouldBe` True
    it "Testing 0 == 0 " $ equal zero zero      `shouldBe` True
    it "Testing 1 == 1 " $ equal one one        `shouldBe` True
    it "Testing 2 == 2 " $ equal two two        `shouldBe` True
    it "Testing 3 == 3 " $ equal three three    `shouldBe` True
    it "Testing 4 == 4 " $ equal four four      `shouldBe` True
    it "Testing 5 == 5 " $ equal five five      `shouldBe` True
    it "Testing 5 == {0} \\/ 5" $ equal (Cons zero five)    five `shouldBe` True
    it "Testing 5 == {1} \\/ 5" $ equal (Cons one five)     five `shouldBe` True
    it "Testing 5 == {2} \\/ 5" $ equal (Cons two five)     five `shouldBe` True
    it "Testing 5 == {3} \\/ 5" $ equal (Cons three five)   five `shouldBe` True
    it "Testing 5 == {4} \\/ 5" $ equal (Cons four five)    five `shouldBe` True
    it "Testing 5 /= {5} \\/ 5" $ equal (Cons five five)    five `shouldBe` False
    it "Testing 0 : 5"  $ belong zero five  `shouldBe` True
    it "Testing 1 : 5"  $ belong one five   `shouldBe` True
    it "Testing 2 : 5"  $ belong two five   `shouldBe` True
    it "Testing 3 : 5"  $ belong three five `shouldBe` True
    it "Testing 4 : 5"  $ belong four five  `shouldBe` True
    it "Testing ¬5 : 5" $ belong five five  `shouldBe` False



