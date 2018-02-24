import Prelude hiding ((==))
import qualified Prelude as P ((==))

data Tree a = Leaf | Node (Tree a) a (Tree a) | Node' [Tree a]


instance (Eq a) => Eq (Tree a) where
(==) Leaf Leaf                      = True
(==) (Node t1 x t2) (Node s1 y s2)  = (t1 == t2) && (x P.== y) && (s1 == s2)
(==) (Node' xs) (Node' ys)          = and $ zipWith (==) xs ys
(==) _ _                            = False
(/=) t1 t2 = not (t1 == t2)



isValid :: Eq a => Tree a -> Bool
isValid Leaf            = True
isValid (Node' ts)      = and $ map isValid ts
isValid (Node t1 _ t2)  = t1 /= t2 





