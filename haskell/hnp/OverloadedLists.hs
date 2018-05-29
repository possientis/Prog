{-# LANGUAGE OverloadedLists #-}

import qualified Data.Map as M

dict :: M.Map String Int
dict = [("foo", 1), ("bar",2)] 


main :: IO ()
main = do
    print $ M.lookup "foo" dict -- Just 1

