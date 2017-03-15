import Prelude hiding ((&&), fst, head, tail)

(&&) :: Bool -> Bool -> Bool
False && _ = False
True  && x  = x

-- It would be difficult to define 'fst' without pattern matching
fst :: (a,b) -> a
fst (x, _) = x


head :: [a] -> a
head [] = error "head: empty list"
head (x:xs) = x

tail :: [a] -> [a]
tail [] = error "tail: empty list"
tail (x:xs) = xs 
