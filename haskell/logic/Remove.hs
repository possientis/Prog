module  Remove
    (   remove
    )   where


remove :: (Eq a) => a -> [a] -> [a]
remove x = filter (/= x) 
