module  Traversal
    (   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11, ex12, ex13, ex14, ex15, ex16
    )   where

import Data.Char        (toUpper)
import Data.Tree
import Control.Lens

import qualified Data.Map as M

ex1 :: [String]
ex1 = ("Bubbles","Buttercup") ^.. both

ex2 :: (String, String)
ex2 = over both (++ "!") ("Bubbles","Buttercup")

ex3 :: (String, String)
ex3 = ("Bubbles","Buttercup") & both %~ (++ "!")

ex4 :: (String, String)
ex4 = ("Bubbles","Buttercup") & both .~ "Blossom"

ex5 :: (Int, Int)
ex5 = ("Bubbles","Buttercup") & both %~ length

ex6 :: (Int, Int, Int)
ex6 = (1,2,3) & each %~ (*10)

ex7 :: [Int]
ex7 = [1,2,3] & each %~ (*10)

ex8 :: String
ex8 = "Here's Johnny" & each %~ toUpper

ex9 :: [Int]
ex9 = [1,2,3,4,5] & taking 3 traversed *~ 10

ex10 :: [Int]
ex10 = [1,2,3,4,5] & dropping 3 traversed *~10

ex11 :: String
ex11 = "once upon a time - optics became  mainstream"
     & takingWhile (/= '-') traversed 
     %~ toUpper

ex12 :: [Int]
ex12 =  [1,2,3,4,5]
     & traversed . filtered even
     *~ 10

ex13 :: (String, String)
ex13 = ("short", "really long")
     & both . filtered ((>5) . length)
     %~ reverse


-- simplified
-- traversed :: Traversable f => Traversal (f a) (f b) a b 

-- real
-- traversed :: Traversable f => IndexedTraversal Int (f a) (f b) a b

ex14 :: [Int]
ex14 = [1,2,3] & traversed *~ 10

-- Tuple are traversable over their last slot
ex15 :: (String, String)
ex15 = ("Batman", "Superman") & traversed %~ take 3

powerLevels :: M.Map String Int
powerLevels = M.fromList
    [("Gohan", 710)
    ,("Goku", 9001)
    ,("Krillin", 5000)
    ,("Piccolo", 408)
    ]

ex16 :: M.Map String String
ex16 = powerLevels 
     & traversed 
     %~ \n -> if n > 9000 then "Over 9000" else show n

opticsTree :: Tree String
opticsTree = Node "Lens" [Node "Fold" [], Node "Traversal" []]

ex17 :: Tree String
ex17 = opticsTree
     & traversed
     %~ reverse


