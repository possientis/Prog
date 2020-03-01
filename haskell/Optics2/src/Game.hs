{-# LANGUAGE TemplateHaskell    #-}

module  Game
    (   amount
    ,   material
    ,   ex1
    ,   ex2
    ,   ex3
    ,   Two     (..)
    ,   Three   (..)
    ,   Five    (..)
    ,   Eight   (..)
    ,   dominoTrain
    )   where

import Control.Lens

data Player  = Player   deriving Show
data Wool    = Wool     deriving Show
data Sweater = Sweater  deriving Show

data Item a = Item
    { _material :: a
    , _amount   :: Int
    } deriving Show

makeLenses ''Item

weave :: Wool -> Sweater
weave Wool = Sweater

gameState :: (Player, Item Wool)
gameState =  (Player, Item Wool 5)


ex1 :: (Player, Item Sweater)
ex1 = over (_2 . material) weave gameState

materialL :: Lens (other, Item a) (other, Item b) a b
materialL = _2 . material

ex2 :: (Player, Item Sweater)
ex2 = over materialL weave gameState

ex3 :: String
ex3 = view (_2 . _1 . _2) ("Ginerva", (("Galileo", "Waldo"), "Malfoy"))

data Five  = Five
data Eight = Eight
data Two   = Two
data Three = Three

fiveEightDomino :: Lens' Five Eight
fiveEightDomino = lens getter setter where
    getter   = const Eight
    setter _ = const Five

mysteryDomino   :: Lens' Eight Two
mysteryDomino = lens getter setter where
    getter   = const Two
    setter _ = const Eight

twoThreeDomino  :: Lens' Two Three
twoThreeDomino = lens getter setter where
    getter   = const Three
    setter _ = const Two

dominoTrain :: Lens' Five Three
dominoTrain = fiveEightDomino . mysteryDomino . twoThreeDomino

