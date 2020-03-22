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
deck =  [Card "Skortul"     Wet False   [Move "Squirt" 20]
        ,Card "Scorchander" Hot False   [Move "Scorch" 20]
        ]
