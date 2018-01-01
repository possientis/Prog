{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Type.Equality

type family If (p :: Bool) (a :: k) (b :: k) :: k where
    If True a b     = a
    If False a b    = False 


type family Lookup (k :: a) (ls :: [(a,b)]) :: Maybe b where
    Lookup k '[]    = 'Nothing
    Lookup k ('(a,b) ': xs) = If (a == k) ('Just b) (Lookup k xs)

-- TODO


    

