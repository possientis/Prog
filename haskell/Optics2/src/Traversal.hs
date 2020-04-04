module  Traversal
    (   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11, ex12, ex13, ex14, ex15, ex16, ex17, ex18, ex19, ex20
    ,   ex21, ex22, ex23, ex24, ex25, ex26, ex27, ex28, ex29, ex30
    ,   ex31, ex32, ex33, ex34, ex35, ex36
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


-- simple
-- worded :: Traversal' String String
-- lined  :: Traversal' String String

-- real
-- worded :: Applicative f => IndexedLensLike' Int f String String
-- lined  :: Applicative f => IndexedLensLike' Int f String String

ex18 :: [String]
ex18 = "I'll be back!" ^.. worded 

ex19 :: [String]
ex19 = "Run\nForrest\nRun" ^.. lined

-- surroundeach word with '*'s
ex20 :: String
ex20 = "blue suede shoes" & worded %~ \s -> "*" ++ s ++ "*"

ex21 :: String
ex21 = "blue suede shoes" & worded %~ \(x:xs) -> toUpper x : xs

-- add a '#' at the start of each line
ex22 :: String
ex22 = "blue\nsuede\nshoes" & lined %~ ('#':)


-- simple
-- beside :: Traversal s t a b -> Traversal s' t' a b -> Traversal (s,s') (t,t') a b
-- beside :: Lens s t a b -> Lens s' t' a b -> Traversal (s,s') (t,t') a b
-- beside :: Fold s a -> Fold s' a -> Fold (s,s') a

dinos :: (String, (Int, String))
dinos = ("T-Rex", (42, "Stegosaurus"))

ex23 :: [String]
ex23 = dinos ^.. beside id _2


numbers :: ([(Int,Int)], [Int])
numbers = ([(1,2),(3,4)],[5,6,7])

ex24 :: [Int]
ex24 = numbers ^.. beside (traversed . both) traversed

ex25 :: [String]
ex25 = ("T-Rex", ("Ankylosaurus","Stegosaurus")) ^.. beside id both

ex26 :: (String, [String])
ex26 = ("Cowabunga", ["let's", "order", "pizza"])
     & beside traversed (traversed . traversed)
     %~ toUpper

traversal1 :: Traversal' (Either (Int, Int) [Int]) Int
traversal1 = beside both traversed

ex27 :: Either (Int, Int) [Int]
ex27 = Left (1, 2) & traversal1 %~ negate


ex28 :: Either (Int, Int) [Int]
ex28 = Right [3,4] & traversal1 %~ negate

-- element :: Traversable f => Int -> Traversal' (f a) a


ex29 :: Maybe Int
ex29 = [0,1,2,3,4] ^? element 2

ex30 :: [Int]
ex30 = [0,1,2,3,4] & element 2 %~ (*100)

-- elementOf :: Traversal' s a -> Int -> Traversal' s a
-- elementOf :: Fold s a       -> Int -> Fold s a


-- element is basically 'elementOf traversed'
ex31 :: Maybe Int
ex31 = [0,1,2,3,4] ^? elementOf traversed 2


ex32 :: Maybe Int
ex32 = [[0,1,2],[3,4],[5,6,7,8]] ^? elementOf (traversed . traversed) 6

ex33 :: [[Int]]
ex33 = [[0,1,2],[3,4],[5,6,7,8]] & elementOf (traversed . traversed) 6 %~ (*100)


ex34 :: String
ex34 = "blue suede shoes" & worded . taking 1 traversed %~ toUpper

ex35 :: [String]
ex35 = ["short","really long"]
     & traversed 
     . filtered ((>5) . length)
     . worded 
     %~ \s -> "*" ++ s ++ "*"

ex36 :: ((String,Int),(String,Int),(String,Int))
ex36 = (("Ritchie",100000), ("Archie",32), ("Reggie",4350))
     & each 
     . filtered ((> 1000) . snd)
     . _1
     %~ ("Rich " ++)
