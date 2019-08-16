import Data.Vect

anyVect : (n : Nat ** Vect n String)
anyVect = (3 ** ["Rod","Jane","freddy"])


readVect : IO (n ** Vect n String)
readVect = do
  x <- getLine
  if (x == "")
     then pure (_ ** [])
     else do
       (_ ** xs) <- readVect
       pure (_ ** x :: xs)


main : IO ()
main = do
  putStrLn "Input your first vector"
  (n ** xs) <- readVect
  putStrLn "Input your second vector"
  (m ** ys) <- readVect
  case exactLength n ys of
       Nothing  => putStrLn "The two vectors have different lengths"
       Just ys' => printLn $ zip xs ys'
