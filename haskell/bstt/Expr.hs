data L a 
    = Var a
    | Lam a (L a)
    | App (L a) (L a)


newtype V = V { unVar :: Int } deriving (Eq, Ord)


type Expr = L V 

remove :: (Eq a) => a -> [a] -> [a]

remove a  []                = [] 
remove a  (x:xs) | a == x   =     remove a xs
remove a  (x:xs) | a /= x   = x : remove a xs


free :: (Eq a) => L a -> [a]
free (Var x)   = [x]
free (Lam x p)  = remove x (free p) 
free (App p q)  = free p ++ free q

-- provides ability to pick smallest element not in given list 
class (Ord a, Eq a) => Choose a where
    choose :: [a] -> a  

instance Choose V where
    choose xs = chooseFrom 0 xs 
        where
        chooseFrom :: Int -> [V] -> V
        chooseFrom n xs = if (V n) `elem` xs 
            then chooseFrom (n+1) xs
            else (V n)
-- subst N x M = [N/x](M) (M with N in place of x)    
subst :: (Choose a) => L a -> a -> L a -> L a
subst p x (Var y)   = if x == y then p else (Var y)
subst p x (App q r) = App (subst p x q) (subst p x r)
subst p x (Lam y q)
    | x == y                = Lam y q
    | x /=y 
    , not (elem x (free q)) = Lam y q
    | x /= y
    , elem x (free q)
    , not (elem y (free p)) = Lam y (subst p x q)
