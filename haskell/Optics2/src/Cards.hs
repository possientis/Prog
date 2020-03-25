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
    ,   ex1, ex2, ex3, ex4, ex5
    )   where

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
