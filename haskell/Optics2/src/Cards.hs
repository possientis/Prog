{-# LANGUAGE TemplateHaskell    #-}

module Cards 
    (   Card
    ,   name
    ,   aura
    ,   holo
    ,   moves
    ,   moveName
    ,   movePower
    ,   deck
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11
    )   where

import Data.Ord         (comparing)
import Control.Lens

data Card = Card
    { _name  :: String
    , _aura  :: Aura
    , _holo  :: Bool
    , _moves :: [Move]
    } deriving (Show, Eq)

data Aura = Wet | Hot | Spark | Leafy 
    deriving (Show, Eq)

data Move = Move
    { _moveName  :: String
    , _movePower :: Int
    } deriving (Show, Eq)

makeLenses ''Card
makeLenses ''Move


deck :: [Card]
deck =  [Card "Skortul"     Wet     False   [Move "Squirt"          20]
        ,Card "Scorchander" Hot     False   [Move "Scorch"          20]
        ,Card "Seedasaur"   Leafy   False   [Move "Allergize"       20]
        ,Card "Kapichu"     Spark   False   [Move "Poke"            10
                                            ,Move "Zap"             30]
        ,Card "Elecdude"    Spark   False   [Move "Asplode"         50]
        ,Card "Garydose"    Wet     True    [Move "Gary's move"     40]
        ,Card "Moisteon"    Wet     False   [Move "Soggy"            3]
        ,Card "Grasseon"    Leafy   False   [Move "Leaf Cut"        30]
        ,Card "Spicyeon"    Hot     False   [Move "Capsaicisize"    40]
        ,Card "Sparkeon"    Spark   True    [Move "Shock"           40
                                            ,Move "Battery"         50]
        ]

-- How many Spark cards do I have
ex1 :: Int
ex1 = lengthOf (folded . aura . filtered (== Spark)) deck

-- How many moves have an attack power above 30
ex2 :: Int
ex2 = lengthOf (folded . moves . folded . movePower . filtered (> 30)) deck

-- List all cards which have any move with an attack power greater than 40
ex3 :: [String]
ex3 = deck 
    ^.. folded 
      . filtered (anyOf (moves . folded . movePower) (>40)) 
      . name

-- How many moves do my Spark cards have in total
ex4 :: Int
ex4 = lengthOf ( folded     -- fold over each card
               . filtered ((== Spark) . _aura)
               . moves      -- select moves
               . folded     -- fold over all moves
               ) deck


-- List all my Spark moves with a power greater than 30
ex5 :: [String]
ex5 = toListOf ( folded     -- fold over each card
               . filtered ((== Spark) . _aura)
               . moves
               . folded
               . filtered ((>30) . _movePower)
               . moveName
               ) deck

{- Need a more recent version of lens
ex6 :: [String]
ex6 = deck
    ^.. folded
      . filteredBy (aura . only Spark)
      . moves
      . folded
      . filteredBy (movePower . filtered (> 30))
      . moveName
-}


ex6 :: Maybe ()
ex6 = 1 ^? only (1 :: Int)


ex7 :: Maybe ()
ex7 = 2 ^? only (1 :: Int)

ex8 :: Bool
ex8 = has (only "needle") "needle"

ex9 :: Bool
ex9 = has (only "needle") "haystack"

ex10 :: Maybe Card
ex10 = maximumByOf
    (folded . filtered _holo)
    (comparing (lengthOf moves))
    deck

ex11 :: [String]
ex11 = deck 
    ^.. folded
      . filtered ((=='S') . head . _name)
      . name

