import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck
import Data.Hashable
import System.Process


class IShape a where
  draw :: a -> IO ()
  getShape :: String -> a

data Rectangle = Rectangle
data Circle = Circle

instance IShape Rectangle where
  draw r = putStrLn "Rectangle"
  getShape "Rectangle" = Rectangle

instance IShape Circle where
  draw r = putStrLn "Circle"
  getShape "Circle" = Circle

main = do 
  draw (getShape "Rectangle")


