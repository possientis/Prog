{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeLits
import Data.Proxy
import GHC.Exts (Constraint)

-- type-level functions over type-level lists
type family Reverse (xs :: [k]) :: [k] where
    Reverse '[] = '[]
    Reverse xs  = Rev xs '[]

type family Rev (xs :: [k]) (ys :: [k]) :: [k] where
    Rev '[] i       = i
    Rev (x ': xs) i = Rev xs (x ': i)


type family Length (as :: [k]) :: Nat where
    Length '[]          = 0
    Length (x ': xs)    = 1 + Length xs

type family If (p :: Bool) (a :: k) (b :: k) :: k where
    If True  a b = a
    If False a b = b


type family Concat (as :: [k]) (bs :: [k]) :: [k] where
--    Concat a '[]        = a   -- why is this here ?
    Concat '[] b        = b
    Concat (a ': as) bs = a ': Concat as bs
    
type family Map (f :: a -> b) (as :: [a]) :: [b] where
    Map f '[]       = '[]
    Map f (x ': xs) =  f x ': Map f xs

type family Sum (xs :: [Nat]) :: Nat where
    Sum '[]         = 0
    Sum (x ': xs)   = x + Sum xs 

ex1 :: Reverse [1,2,3] ~ [3,2,1] => Proxy a
ex1 = Proxy

ex2 :: Length [1,2,3] ~ 3 => Proxy a
ex2 = Proxy


ex3 :: (Length [1,2,3]) ~ (Length (Reverse [1,2,3])) => Proxy a
ex3 = Proxy

-- reflecting type-level computations back to the value level

ex4 :: Integer
ex4 = natVal (Proxy :: Proxy (Length (Concat [1,2,3] [4,5,6])))

ex5 :: Integer
ex5 = natVal (Proxy :: Proxy (Sum [1,2,3]))

type family Elem (a :: k) (bs :: [k]) :: Constraint where
    Elem a (a ': bs) = (() :: Constraint)
    Elem a (b ': bs) = a `Elem` bs

