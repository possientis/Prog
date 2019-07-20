module MergeSort
    (   main
    )   where

insert :: (Ord a) => a -> [a] -> [a]
insert a []     = [a]
insert a (x:xs) = if a <= x then a:x:xs else x:insert a xs 



merge :: (Ord a) => [a] -> [a] -> [a]
merge xs []     = xs
merge xs (y:ys) = insert y $ merge xs ys    

split :: [a] -> ([a],[a])
split []        = ([],[])
split [x]       = ([x],[])
split (x:y:xs)  = let (l1,l2) = split xs in (x:l1,y:l2)

mergeSort :: (Ord a) => [a] -> [a]
mergeSort []    = []
mergeSort [x]   = [x]
mergeSort xs    = let (l1,l2) = split xs in
    merge (mergeSort l1) (mergeSort l2)


-- so bad: 'sort' of Data.List does so much better here
main :: IO ()
main = do
    print $ mergeSort $ reverse ([1..10000] :: [Int])
