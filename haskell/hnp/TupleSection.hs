{-# LANGUAGE TupleSections #-}




main :: IO ()
main = do
    print $ (1,2) == (,) 1 2
    {- LANGUAGE TupleSections -}
    print $ (1,2) == (1,) 2
    print $ (1,2) == (,2) 1
    print $ (,2,) 1 3 == (1,2,3)
    print $ map (,"tag") [1,2,3] == [(1,"tag"),(2,"tag"),(3,"tag")]
