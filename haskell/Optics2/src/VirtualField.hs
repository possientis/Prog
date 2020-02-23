{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module  VirtualField
    (   location
    ,   celsius
    ,   fahrenheit  -- virtual field
    ,   Temperature   
    ,   Celsius     (..)
    ,   Fahrenheit   (..)
    ,   ex1
    ,   ex2
    ,   ex3
    )   where


import Control.Lens

newtype Celsius = Celsius { unCelsius :: Float }
    deriving (Show, Num)

newtype Fahrenheit = Fahrenheit { unFahrenheit :: Float }
    deriving (Show, Num)

data Temperature = Temperature
    { _location :: String
    , _celsius  :: Celsius
    } deriving (Show)

makeLenses ''Temperature

toCelsius :: Fahrenheit -> Celsius
toCelsius (Fahrenheit f) = Celsius $ (f - 32) * (5/9)

fromCelsius :: Celsius -> Fahrenheit
fromCelsius (Celsius c) = Fahrenheit $ c * (9/5) + 32

fahrenheit :: Lens' Temperature Fahrenheit
fahrenheit = lens getFahrenheit setFahrenheit where
    getFahrenheit = fromCelsius . view celsius
    setFahrenheit s f = set celsius  (toCelsius f) s


temp :: Temperature
temp = Temperature "Berlin" (Celsius 7.0)

ex1 :: Fahrenheit
ex1 = view fahrenheit temp

ex2 :: Temperature
ex2 = set fahrenheit (Fahrenheit 56.3) temp

ex3 :: Temperature
ex3 = over fahrenheit (+ (Fahrenheit 18)) temp

