import Data.Vect

addMatrix : (Num a) 
  => Vect n (Vect m a) 
  -> Vect n (Vect m a) 
  -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

transposeMat : Vect n (Vect m a) -> Vect m (Vect n a)
transposeMat []        = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)

dot : (Num a) => Vect n a -> Vect n a -> a
dot [] [] = 0
dot (x :: xs) (y :: ys) = (x * y) + dot xs ys


mulMatrix : (Num a) 
  => Vect n (Vect m a) 
  -> Vect m (Vect p a) 
  -> Vect n (Vect p a)
mulMatrix xs ys = 
  let zs = transposeMat ys in 
    map (\v => map (dot v) zs) xs 

createEmpties : Vect n (Vect 0 a)
createEmpties = replicate _ []

createEmpties' : {n : Nat} -> Vect n (Vect 0 a)
createEmpties' {n} = replicate n []

main : IO ()
main = do
  printLn $ addMatrix
    [[1,2,3],[4,5,6]]
    [[7,8,9],[1,2,3]]

  printLn $ transposeMat [[1,2,3],[4,5,6]]

  printLn $ mulMatrix [[1,2],[3,4],[5,6]] [[7,8,9,10],[11,12,13,14]]
