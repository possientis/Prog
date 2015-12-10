import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck
import Data.Hashable
import System.Process

main :: IO ()
main = do
  putStrLn "What is your name?"
  name <- getLine
  putStrLn ("Nice  to meet you, " ++ name ++ "!")
