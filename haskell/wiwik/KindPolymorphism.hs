{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE PolyKinds #-}

app :: forall a b. (a -> b) -> a -> b
app f a = f a

-- doing the same at the type level ?

-- without PolyKinds :
-- TApp :: (* -> *) -> * -> *
-- with PolyKinds
-- TApp :: (k -> *) -> k -> *

data TApp f a = MkTApp (f a)


-- Default   : Mu :: ((* -> *) -> (* -> *)) -> (* -> *)
-- PolyKinds : Mu :: ((k -> *) -> (k -> *)) -> (k -> *) 

data Mu f a = Roll (f (Mu f) a)

-- Default   : Proxy :: * -> *
-- PolyKinds : Proxy :: k -> *

data Proxy a = Proxy


data Rep = Rep

class PolyClass a where
    foo :: Proxy a -> Rep
    foo = const Rep

-- ()       :: *
-- []       :: * -> *
-- Either   :: * -> * -> *

instance PolyClass ()
instance PolyClass []
instance PolyClass Either

newtype I (a :: *) = I a

newtype K (a :: *) (b :: k) = K a

newtype Flip (f :: k1 -> k2 -> *) (x :: k2) (y :: k1) = Flip (f y x)

unI :: I a -> a
unI (I x) = x


unK :: K a b -> a
unK (K x) = x

unFlip :: Flip f x y -> f y x
unFlip (Flip x) = x




