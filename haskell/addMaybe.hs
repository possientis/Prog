import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck
import Data.Hashable
import System.Process

add :: Maybe Int -> Maybe Int -> Maybe Int
add mx my =
  case mx of
    Nothing -> Nothing
    Just x  -> case my of
                Nothing -> Nothing
                Just y  -> Just (x + y)

add2 :: Maybe Int -> Maybe Int -> Maybe Int
add2 mx my =
  mx >>= (\x ->
    my >>= (\y ->
      return (x + y)))

add3 :: Maybe Int -> Maybe Int -> Maybe Int
add3 mx my = do
  x <- mx
  y <- my
  return (x + y)
 
add4 :: Maybe Int -> Maybe Int -> Maybe Int
add4 mx my = do {
  x <- mx;
  y <- my;
  return (x + y)
  }
 
add5 :: Maybe Int -> Maybe Int -> Maybe Int
add5 = liftM2 (+)

