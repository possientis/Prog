{-# LANGUAGE KindSignatures, ExplicitForAll, GADTs #-}

import Prelude hiding (id)

id :: forall (a :: *). a -> a
id x = x



main :: IO ()
main = do
    print $ id 3


data Term a :: * where
    Lit     :: a -> Term a
    Succ    :: Term Int -> Term Int
    IsZero  :: Term Int -> Term Bool
    If      :: Term Bool -> Term a -> Term a -> Term a 


data Vec :: * -> * -> * where
    Nil     :: Vec n a
    Cons    :: a -> Vec n a -> Vec n a


data Fix :: (* -> *) -> * where
    In :: f (Fix f) -> Fix f
