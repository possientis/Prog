import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck

check :: Int -> Bool
check n = True

check2 :: [Int] -> Bool
check2 xs = (xs == reverse (reverse xs))

check3 :: [Int] -> [Int] -> Bool
check3 xs ys = reverse (xs ++ ys) == (reverse ys ++ reverse xs)

-- either type 'main' from ghci or compile and run
main = quickCheck check2 >> quickCheck check3
