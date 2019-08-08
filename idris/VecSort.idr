import Data.Vect

insert : (Ord a) => a -> Vect len a -> Vect (S len) a
insert x []        = [x]
insert x (y :: xs) = 
  if x < y 
     then x :: y :: xs
     else y :: insert x xs


-- insertion sort
insSort : (Ord a) => Vect n a -> Vect n a
insSort []        = []
insSort (x :: xs) = insert x (insSort xs)

main : IO ()
main = do
  putStrLn $ show $ insSort [9,0,1,3,7,1,4,8,6,0,5]


