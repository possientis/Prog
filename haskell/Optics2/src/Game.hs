{-# LANGUAGE TemplateHaskell    #-}

module  Game
    (   amount
    ,   material
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
