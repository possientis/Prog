{-# LANGUAGE TypeFamilies #-}

import Data.Set hiding (singleton)
import qualified Data.Set as Set (singleton)
import Data.ByteString
import Data.Vector

-- type family is simply a function on types

type family F1 a where  -- closed definition
    F1 Int = Bool
    F1 Char = Double


useF1 :: F1 Int -> F1 Char
useF1 True  =  1.0
useF1 False = (-1.0)


type family Elements c  -- open definition

class Collection c where
    singleton :: Elements c -> c



type instance Elements [a] = a

instance Collection [a] where
    singleton x = [x]


type instance Elements (Set a) = a

instance Collection (Set a) where
    singleton  = Set.singleton


class Collection' c where
    type Elements' c
    singleton' :: Elements' c -> c

instance Collection' [a] where
    type Elements' [a] = a
    singleton' x = [x]

instance Collection' (Set a) where
    type Elements' (Set a) = a
    singleton' = Set.singleton


type family F2 a

type instance F2 Int = Bool


-- a data family defines a family of datatypes

data family Array a     -- compact storage of elements of type a

data instance Array Bool = MkArrayBool ByteString
data instance Array Int  = MkArrayInt (Vector Int)



