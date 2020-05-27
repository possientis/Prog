module  Normal
    (   normal
    ,   toInt
    ,   showSet
    ,   main
    )   where

import Set
import Elem
import Insert

import Test.QuickCheck

instance Show Set where
    show = showSet

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

normal :: Set -> Set
normal Nil = Nil
normal (Cons x xs)
    | x <: xs   = normal xs
    | otherwise = insert (normal x) (normal xs)

toInt :: Set -> Maybe Int
toInt x = case normal x of
    Nil -> Just 0
    (Cons y ys) -> 
        if y == ys 
            then case toInt y of
                Nothing -> Nothing
                Just n  -> Just (n + 1)
            else Nothing

showSet :: Set -> String
showSet x = case toInt x of
    Just n  -> show n
    Nothing -> "{" ++ (showL $ toList (normal x)) ++ "}"
    where
        showL :: [Set] -> String
        showL [] = ""
        showL [y] = showSet y
        showL (y : ys) = showSet y ++ "," ++ showL ys
