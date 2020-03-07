{-# LANGUAGE TemplateHaskell    #-}

module  View
    (   cargo
    ,   weightKilos
    ,   payload
    ,   serenity
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10
    ,   ex11, ex12, ex13, ex14, ex15, ex16
    ,   temperature
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

ex7 :: Ship
ex7 = serenity
    & payload . cargo .~ "Chocolate"
    & payload . weightKilos .~ 2310

ex8 :: Ship
ex8 = serenity 
    & set (payload . cargo) "Chocolate"
    & set (payload .weightKilos) 2310

ex9 :: Ship
ex9 = serenity
    & payload . weightKilos %~ subtract 1000
    & payload . cargo .~ "Chocolate"

ex10 :: (Int, Int)
ex10 = (2,30) & _2 +~ 5                 -- (2,35)

ex11 :: (Int,Double)
ex11 = (2,30) & _2 //~ 2                -- (2,15.0)

ex12 :: (Int, Int)
ex12 = (2,30) & _1 ^~ (3 :: Int)        -- (8,30)

ex13 :: (Bool, Int)
ex13 = (False, 30) & _1 ||~ True        -- (True, 30)

ex14 :: (String, Int)
ex14 = ("abra", 30) & _1 <>~ "cadabra"  -- ("abracadabra", 30)


data Thermometer = Thermometer
    { _temperature :: Int
    } deriving (Show)

makeLenses ''Thermometer

ex15 :: (Int, Thermometer)
ex15 = Thermometer 20 & temperature <+~ 15  -- (35,Thermometer 35)

ex16 :: (Int, Thermometer)
ex16 = Thermometer 20 & temperature <<+~ 15  -- (20,Thermometer 35)

