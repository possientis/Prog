import Control.Monad
import System.Directory

add' :: Maybe Int -> Maybe Int -> Maybe Int
add' mx my = 
  mx >>= (\x -> 
    my >>= (\y -> 
      return (x + y)))

add'' :: Maybe Int -> Maybe Int -> Maybe Int
add'' mx my = do
  x <- mx
  y <- my
  return (x +y)


add :: Maybe Int -> Maybe Int -> Maybe Int
add =liftM2 (+)

