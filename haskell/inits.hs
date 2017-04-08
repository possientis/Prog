import Data.List

myInits :: [a] ->[[a]]
myInits = map reverse . scanl (flip (:)) []

-- equivalently
--myInits xs = map reverse . scanl (flip (:)) [] $ xs


main :: IO ()
main = do
  putStrLn $ show $ inits   [1,2,3] -- [[],[1],[1,2],[1,2,3]]
  putStrLn $ show $ myInits [1,2,3] -- [[],[1],[1,2],[1,2,3]]
