-- reverse is a fold
import Data.List hiding (reverse)
import Prelude hiding (reverse)
import System.IO

reverse :: [a] -> [a]
reverse = foldl (flip (:))  []

main = do 
  putStrLn "Benchmarking has started..."
  hFlush stdout
  seq (reverse [1..10000000]) putStrLn "done"


