{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality

type family If (p :: Bool) (a :: k) (b :: k) :: k where
    If True a b     = a
    If False a b    = False 


type family Lookup (k :: a) (ls :: [(a,b)]) :: Maybe b where
    Lookup k '[]    = 'Nothing
    Lookup k ('(a,b) ': xs) = If (a == k) ('Just b) (Lookup k xs)

type M  =   [   '("a",1)
            ,   '("b",2)
            ,   '("c",3)
            ,   '("d",4)
            ]


type K = "a"

type (!!) m (k :: Symbol) a = (Lookup k m) ~ Just a


value :: Integer
value = natVal ( Proxy :: (M !! "a") a => Proxy a)

    

