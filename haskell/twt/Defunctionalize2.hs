{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ExplicitForAll         #-}

import Data.Kind

-- Given a kind k, defines a kind 'Exp k'
type Exp k = k -> Type

-- A type 'e' of kind 'Exp k' can be evaluated as a type of kind k
-- Signature for type-level function Eval :: Exp k -> k
-- But no implementation provided for this type-level function
-- Defined as an open type family
type family Eval (e :: Exp k) :: k

-- Given two kinds k1 k2, given a type of kind (k1,k2), 
-- creates a type of kind Exp k2
data Snd :: forall k1 k2. (k1,k2) -> Exp k2

-- Same with GADTs syntax?
data Snd' (a :: (k1,k2)) :: Exp k2

-- So both Ex1 and Ex1' are types of kind 'Exp *'
type Ex1  = Snd  '(Int,String)
type Ex1' = Snd' '(Int,String) 

type instance Eval (Snd  '(a,b)) = b
type instance Eval (Snd' '(a,b)) = b

-- kind! Ex2 = [Char] :: *
type Ex2  = Eval Ex1
type Ex2' = Eval Ex1'

data FromMaybe :: forall k. k -> Maybe k -> Exp k

-- kind! Ex3 = Ex3 :: * -> Type  
type Ex3 = FromMaybe Int ('Just Double)
type Ex4 = FromMaybe Int ('Nothing )

type instance Eval (FromMaybe _ ('Just a))  = a
type instance Eval (FromMaybe a 'Nothing)   = a

type Ex5 = Eval Ex3





data ListToMaybe :: [a] -> Exp (Maybe a)
type instance Eval (ListToMaybe '[])        = 'Nothing
type instance Eval (ListToMaybe (a ': as))  = 'Just a


data MapList :: (a -> Exp b) -> [a] -> Exp [b]


