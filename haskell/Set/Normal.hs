module  Normal
    (   normal
    ,   normal2
    ,   toInt
    ,   showSet
    ,   main
    )   where

import Data.List        hiding (insert)

import Set
import Elem
import Insert

--instance Show Set where
--    show = showSet

normal :: Set -> Set
normal Nil = Nil
normal (Cons x xs)
    | x <: xs   = normal xs
    | otherwise = insert (normal x) (normal xs)


order :: Set -> Set -> Ordering
order x y = if x <= y then GT else LT 

normal2 :: Set -> Set
normal2 = fromList . sortBy order . nub . map normal2 . toList

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
