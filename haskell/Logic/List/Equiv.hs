module  List.Equiv
    (   (===)
    ,   (/==)
    )   where

import List.Include

infix 3 ===

(===) :: (Eq a) => [a] -> [a] -> Bool
(===) xs ys = (xs <== ys) && (ys <== xs)


(/==) :: (Eq a) => [a] -> [a] -> Bool
(/==) xs ys = not $ xs === ys
