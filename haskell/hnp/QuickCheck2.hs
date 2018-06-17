{-# LANGUAGE TemplateHaskell #-}

import Test.QuickCheck (quickCheckAll)
import Data.List (sort)


idempotent :: Eq a => (a -> a) -> a -> Bool
idempotent f x = f (f x) == f x

prop_sortIdempotent :: [Int] -> Bool
prop_sortIdempotent = idempotent sort


return []

main = $quickCheckAll
