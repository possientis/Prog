module  Normal
    (   normal
    ,   toInt
    ,   showSet
    )   where

import Set
import Elem
import Insert

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


