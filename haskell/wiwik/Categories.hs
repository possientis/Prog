{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

import Prelude hiding ((.), id, Functor, fmap)

class Category (hom :: k -> k -> *) where
    id  :: hom a a
    (.) :: hom y z -> hom x y -> hom x z

type Hask = (->)

instance Category Hask where
    id x        = x
    (g . f) x   = g (f x)


newtype Op a b = Op (b -> a)

instance Category Op where 
    id = Op id
    (Op f) . (Op g) = Op (g . f)


class (Category homc, Category homd) => Functor homc homd t where
    fmap :: homc a b -> homd (t a) (t b) 


instance Functor Hask Hask [] where
    fmap f []       = []
    fmap f (x:xs)   = f x : fmap f xs


instance Functor Hask Hask Maybe where
    fmap f Nothing  = Nothing
    fmap f (Just x) = Just (f x)


type Nat f g = forall a . f a -> g a


headMay :: Nat [] Maybe
headMay []      = Nothing
headMay (x:xs)  = Just x

