import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck
import Data.Hashable
import System.Process

list = [ (x,y) | x <- [1..10], y <- [1..x] ]

