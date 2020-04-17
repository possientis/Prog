module PartsOf
    (   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11, ex12, ex13, ex14, ex15, ex16
    )   where

import Data.List
import Control.Lens

-- partsOf :: Traversal' s a -> Lens' s [a]

ex1 :: [(Char,Int)]
ex1 =  [('b',2),('a',1),('c',3)]

ex2 :: String
ex2 = ex1 ^. partsOf (traversed . _1)

ex3 :: [Int]
ex3 = ex1 ^. partsOf (traversed . _2)

ex4 :: [(Char,Int)]
ex4 = ex1 & partsOf (traversed . _1) .~ ['c','a','t']

ex5 :: [(Char,Int)]
ex5 = ex1 & partsOf (traversed . _1) .~ ['l','e','o','p','a','r','d']

ex6 :: [(Char,Int)]
ex6 = ex1 & partsOf (traversed . _1) .~ ['l']

ex7 :: [(Char,Int)]
ex7 = ex1 & partsOf (traversed . _1) %~ reverse

ex8 :: [(Char,Int)]
ex8 = ex1 & partsOf (traversed . _1) %~ sort

ex9 :: [(Char,Int)]
ex9 = ex1 & partsOf (traversed . _1) %~ tail

ex10 :: (String, String, String)
ex10 = ("how is a raven", "like a ", "writing desk")
     & partsOf (each . traversed) %~ unwords . sort . words

ex11 :: [String]
ex11 = ("abc","def") ^.. partsOf each . traversed

ex12 :: [String]
ex12 = ("abc","def") ^.. partsOf (each . traversed)

ex13 :: [(Char,Double)]
ex13 = [('a',1),('b',2),('c',3)]
     & partsOf (traversed . _2)
     %~ \xs -> (/sum xs) <$> xs

-- unsafePartsOf :: Traversal s t a b -> Lens s t [a] [b]

ex14 :: [(Bool,Int)]
ex14 = ex1 & unsafePartsOf (traversed . _1) .~ [True,False,True]

-- runtime error
ex15 :: [(Bool,Int)]
ex15 = ex1 & unsafePartsOf (traversed . _1) .~ [True,False]

-- no runtime error
ex16 :: [(Bool,Int)]
ex16 = ex1 & unsafePartsOf (traversed . _1) .~ [True,False, False, True]
