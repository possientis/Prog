{-# LANGUAGE DataKinds #-}

import Data.Proxy

{-
data Proxy a = Proxy -- in Data.Proxy
-}

a :: Proxy ()
a = Proxy


b :: Proxy 3
b = Proxy


c :: Proxy "symbol"
c = Proxy

d :: Proxy Maybe
d = Proxy

e :: Proxy (Maybe ())
e = Proxy


t1 :: a
t1 = undefined

-- better, use scoped type variable

t2 :: Proxy a
t2 = Proxy
