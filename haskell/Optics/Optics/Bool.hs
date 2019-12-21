{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module  Optics.Bool
    (   Sing    (..)
    ,   SBool
    ,   fromSBool 
    )   where

import Optics.Singleton

{-
data SBool (b :: Bool) :: Type where
    STrue  :: SBool 'True
    SFalse :: SBool 'False 
-}

data instance Sing (a :: Bool) where
    STrue  :: Sing 'True
    SFalse :: Sing 'False 

type SBool (a :: Bool) = Sing a

fromSBool :: SBool b -> Bool
fromSBool STrue  = True
fromSBool SFalse = False

instance Show (SBool b) where
    show = show . fromSBool


