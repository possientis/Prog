{-# LANGUAGE TemplateHaskell        #-}

module  VirtualField
    (   location
    ,   celsius
    ,   Temperature   
    )   where


import Control.Lens

data Temperature = Temperature
    { _location :: String
    , _celsius  :: Float
    } deriving (Show)

makeLenses ''Temperature
