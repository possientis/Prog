{-# LANGUAGE TemplateHaskell    #-}

module  View
    (   cargo
    ,   weightKilos
    ,   payload
    ,   serenity
    ,   ex1
    ,   ex2
    ,   ex3
    ,   ex4
    ,   ex5
    ,   ex6
    )   where

import Control.Lens

data Payload = Payload
    { _weightKilos :: Int
    , _cargo       :: String
    } deriving (Show)

makeLenses ''Payload

data Ship = Ship
    { _payload :: Payload
    } deriving (Show)

makeLenses ''Ship

serenity :: Ship
serenity = Ship (Payload 50000 "Livestock")

ex1 :: String
ex1 = view (payload . cargo) serenity

ex2 :: String
ex2 = serenity^.payload.cargo

ex3 :: Ship
ex3 = set (payload . cargo) "Medicine" serenity

ex4 :: Ship
ex4 = serenity&payload.cargo .~ "Medecine" 

ex5 :: Ship
ex5 = payload.cargo .~ "Medecine" $ serenity 

ex6 :: Ship
ex6 = (payload.cargo .~ "Medecine") serenity 
