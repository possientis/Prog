{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}

module  Optics.Singleton
    (   Sing 
    ,   SingE   (..)  
    )   where

data family Sing (a :: k) 


instance Eq (Sing a) where
    (==) _ _ = True


class SingE (a :: k) where
    type Demote a
    fromSing :: Sing a -> Demote a


