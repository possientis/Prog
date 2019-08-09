import Data.Vect

addMatrix : (Num a) => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

{-
mulMatrix : (Num a) => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
mulMatrix [] []        = []
mulMatrix [] (x :: xs) = []
mulMatrix (x :: xs) ys = ?mulMatrix_rhs_2
-}


main : IO ()
main = do
  printLn $ addMatrix
    [[1,2,3],[4,5,6]]
    [[7,8,9],[1,2,3]]
