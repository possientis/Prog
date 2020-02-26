{-# LANGUAGE TemplateHaskell    #-}

module  Nested
    (   name
    ,   address
    ,   streetAddress
    ,   city
    ,   country
    ,   streetNumber
    ,   streetName
    )   where


import Control.Lens

data Person = Person
    { _name    :: String
    , _address :: Address
    } deriving (Show)


data Address = Address
    { _streetAddress :: StreetAddress
    , _city          :: String
    , _country       :: String
    } deriving (Show)

data StreetAddress = StreetAddress 
    { _streetNumber :: String
    , _streetName   :: String
    } deriving (Show)

makeLenses ''Person
makeLenses ''Address
makeLenses ''StreetAddress

