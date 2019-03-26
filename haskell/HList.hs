{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}

import Data.Constraint

infixr 5 :>

data HList (xs :: [*]) where
    Nil  :: HList '[]
    (:>) :: a -> HList as -> HList (a:as)

newtype Username = Username String
newtype Password = Password String
newtype Email    = Email    String
newtype Year     = Year     Int
newtype Month    = Month    Int
newtype Day      = Day      Int
data    Date     = Date Year Month Day

newtype DbText      = DbText        String
newtype DbDate      = DbDate        (Int, Int, Int)
newtype DbEmail     = DbEmail       String
newtype DbPassword  = DbPassword    String


type User = '[Username,Password,Email,Date]

chris :: HList User
chris =  Username "cc" 
      :> Password "ahoy!" 
      :> Email "cc@sm.com" 
      :> Date (Year 1983) (Month 12) (Day 23)
      :> Nil

class Db a where
    type family DbType a
    toDb :: a -> DbType a

instance Db Username where
    type DbType Username = DbText
    toDb (Username s)    = DbText s

instance Db Date where
    type DbType Date = DbDate
    toDb (Date (Year y) (Month m) (Day d)) = DbDate (y,m,d)

instance Db Email where
    type DbType Email = DbEmail
    toDb (Email s)    = DbEmail s

instance Db Password where
    type DbType Password = DbPassword
    toDb (Password s)    = DbPassword s


type family MapDbType (xs :: [*]) :: [*] where
    MapDbType '[]    = '[]
    MapDbType (x:xs) = DbType x : MapDbType xs 

type family All (c :: * -> Constraint) (as :: [*]) :: Constraint where
    All c '[]   = ()
    All c (x : xs) = (c x, All c xs)


mapToDb :: All Db as => HList as -> HList (MapDbType as)
mapToDb Nil       = Nil
mapToDb (a :> as) = toDb a :> mapToDb as


dbChris :: HList (MapDbType User)
dbChris = mapToDb chris


type family Map (f :: a -> b) (xs :: [a]) :: [b] where
    Map _ '[]      = '[]
    Map f (x : xs) = f x : Map f xs

{-
hMap :: forall (c :: * -> Constraint) (f :: * -> *) (as :: [*]) .
    All c as => (forall a . c a => a -> f a) -> HList as -> HList (Map f as)
hMap g []       = []
hMap g (x :> xs) = g x :> hMap @c @f g xs
-}


