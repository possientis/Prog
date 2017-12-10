{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import GHC.Generics
import Test.SmallCheck.Series

data Tree a = Null | Fork (Tree a) a (Tree a)
    deriving (Show, Generic)

instance Serial m a => Serial m (Tree a) -- no need to spell out anything


example :: [Tree ()]
example = list 3 series

depth :: Tree a -> Int
depth Null = 0
depth (Fork l _ r) = 1 + max (depth l) (depth r)


main = do 
    print example
    print $ map depth example
