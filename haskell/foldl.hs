import Prelude hiding (foldl)
import Data.List hiding (foldl, foldl') 

{- tail recursive but due to laziness, op is not evaluated, leading
 - to a big thunk build up which takes space and probably time (memory alloc) 
 -}

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl op acc []       = acc
foldl op acc (x:xs)   = foldl op (op acc x) xs

-- this implementation seems to be as quick as default found in Data.List
foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' op acc []      = acc
foldl' op acc (x:xs)  = let new = op acc x  -- will force evaluation using seq
                        in seq new foldl' op new xs 


-- seriously quicker with strict evaluation (foldl')
-- even with -O2 compile option
main :: IO ()
main = do
  putStrLn $ show $ foldl' (+) 0 [1..5000000]


