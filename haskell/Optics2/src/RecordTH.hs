{-# LANGUAGE TemplateHaskell    #-}

module  RecordTH
    (   name
    ,   numCrew
    ,   Ship    (..)
    )   where

import Control.Lens

data Ship = Ship
    { _name :: String
    , _numCrew :: Int
    } deriving (Show)

makeLenses ''Ship

purplePearl :: Ship
purplePearl = Ship 
    { _name = "Purple Pearl"
    , _numCrew = 38
    }

ex1 :: Int
ex1 = view numCrew purplePearl

ex2 :: String
ex2 = view name purplePearl

ex3 :: Ship
ex3 = set numCrew 41 purplePearl

ex4 :: Ship
ex4 = over numCrew (+5) purplePearl



