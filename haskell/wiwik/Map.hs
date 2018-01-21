import Prelude hiding (lookup)

import Data.Map

kv :: Map Integer String
kv = fromList [(1,"a"),(2,"b")]

lkup :: Integer -> String -> String
lkup key def = case lookup key kv of
    Just val    -> val
    Nothing     -> def


main :: IO ()
main = do
    putStrLn $ lkup 0 "def"
    putStrLn $ lkup 1 "def"
    putStrLn $ lkup 2 "def"


