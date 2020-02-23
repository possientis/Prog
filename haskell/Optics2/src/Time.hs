{-# LANGUAGE TemplateHaskell    #-}

module  Time
    (   Time
    ,   Hours
    ,   Mins
    ,   mkHours
    ,   mkMins
    ,   hours
    ,   mins
    ,   ex1
    ,   ex2
    ,   ex3
    )   where

import Control.Lens

newtype Hours = Hours { _unHours :: Int }
    deriving (Show)

newtype Mins = Mins { _unMins :: Int }
    deriving (Show)

data Time = Time
    { _hours :: Hours
    , _mins  :: Mins
    } deriving (Show)

makeLenses ''Time

mkHours :: Int -> Hours
mkHours h = Hours $ clamp 0 23 h

mkMins :: Int -> Mins
mkMins m = Mins $ clamp 0 59 m

clamp :: Int -> Int -> Int -> Int
clamp minVal maxVal a = min maxVal . max minVal $ a


time :: Time
time = Time (Hours 3) (Mins 10)

ex1 :: Hours
ex1 = view hours time

ex2 :: Time
ex2 = set hours (mkHours 40) time

ex3 :: Time
ex3 = set mins (mkMins (-10)) time
