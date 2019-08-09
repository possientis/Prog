import Data.Vect

myMap : (a -> b) -> List a -> List b
myMap f []        = []
myMap f (x :: xs) = f x :: myMap f xs


myMap' : (a -> b) -> Vect n a -> Vect n b
myMap' f []        = []
myMap' f (x :: xs) = f x :: myMap' f xs


main : IO ()
main = do
  printLn $ myMap  (*2) [1,2,3,4,5,6,7,8,9]
  printLn $ myMap' (*2) [1,2,3,4,5,6,7,8,9]

