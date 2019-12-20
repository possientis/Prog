{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}

module  Optics.Bool
    (   SBool   (..)
    ,   fromSBool
    )   where

import Data.Kind

data SBool (b :: Bool) :: Type where
    STrue  :: SBool 'True
    SFalse :: SBool 'False 

fromSBool :: SBool b -> Bool
fromSBool STrue  = True
fromSBool SFalse = False

instance Eq (SBool b) where
    (==) _ _ = True     -- singleton type

instance Show (SBool b) where
    show = show . fromSBool


