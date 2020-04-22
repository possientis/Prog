{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE TemplateHaskell        #-}

module  Address
    (   Address
    ,   buildingNumber
    ,   streetName
    ,   apartmentNumber
    ,   postalCode
    ,   ex1, ex2, ex3
    )   where

import Control.Lens

data Address = Address
    { _buildingNumber   :: Maybe String
    , _streetName       :: Maybe String
    , _apartmentNumber  :: Maybe String
    , _postalCode       :: Maybe String
    } deriving Show

makeLenses ''Address

data AddressPiece
    = BuildingNumber
    | StreetName
    | ApartmentNumber
    | PostalCode
    deriving Show

type instance Index Address = AddressPiece
type instance IxValue Address = String

-- We need the instance declaration for Ixed,
-- but can leave the implementation blank.
-- It will be implemented automatically in terms of 'At'
instance Ixed Address

instance At Address where
    at :: AddressPiece -> Lens' Address (Maybe String)
    at = \case
        BuildingNumber  -> buildingNumber
        StreetName      -> streetName
        ApartmentNumber -> apartmentNumber
        PostalCode      -> postalCode

addr :: Address
addr  = Address Nothing Nothing Nothing Nothing

ex1 :: Address
ex1 = addr 
    & at StreetName ?~ "Baker St."
    & at ApartmentNumber ?~ "221B"

ex2 :: Address
ex2 = ex1 & ix ApartmentNumber .~ "221A"

ex3 :: Address
ex3 = ex1 & sans StreetName
        
