{-# LANGUAGE TemplateHaskell    #-}

module  Nested
    (   name
    ,   address
    ,   streetAddress
    ,   city
    ,   country
    ,   streetNumber
    ,   streetName
    ,   sherlock
    ,   setStreetNumber
    ,   setStreetNumber'
    ,   setStreetNumber3
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

sherlock :: Person
sherlock = Person
    { _name     = "S. Holmes"
    , _address  = Address
        { _streetAddress = StreetAddress
            { _streetNumber = "221B"
            , _streetName   = "Baker Street"
            }
        , _city    = "London"
        , _country = "England"
        }
    }

-- without using lenses
setStreetNumber :: String -> Person -> Person
setStreetNumber new person = person
    { _address = currentAddress
        { _streetAddress = currentStreetAddress
            { _streetNumber = new }}} 
    where
    currentAddress       = _address (person)
    currentStreetAddress = _streetAddress currentAddress


updateAddress :: (Address -> Address) -> (Person  -> Person)
updateAddress modify person = person
    { _address = modify . _address $ person
    }

updateStreetAddress :: (StreetAddress -> StreetAddress) -> (Address -> Address)
updateStreetAddress modify addr = addr
    { _streetAddress = modify . _streetAddress $ addr
    }

updateStreetNumber :: (String -> String) -> (StreetAddress -> StreetAddress)
updateStreetNumber modify street = street
    { _streetNumber = modify . _streetNumber $ street
    }

setStreetNumber' :: String -> Person -> Person
setStreetNumber' s = updateAddress . updateStreetAddress . updateStreetNumber $ const s

streetNumberL :: Lens' Person String
streetNumberL = address . streetAddress . streetNumber

setStreetNumber3 :: String -> Person -> Person
setStreetNumber3 = set streetNumberL 




