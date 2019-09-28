{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

import Data.Kind


type Exp a = a -> Type

type family Eval (e :: Exp a) :: a

data Snd :: (a,b) -> Exp b
type instance Eval (Snd '(a,b)) = b

data FromMaybe :: a -> Maybe a -> Exp a
type instance Eval (FromMaybe _1 ('Just a)) = a
type instance Eval (FromMaybe a 'Nothing)   = a

data ListToMaybe :: [a] -> Exp (Maybe a)
type instance Eval (ListToMaybe '[])        = 'Nothing
type instance Eval (ListToMaybe (a ': as))  = 'Just a


data MapList :: (a -> Exp b) -> [a] -> Exp [b]

