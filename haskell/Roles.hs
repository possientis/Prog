{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE PolyKinds #-}


data Nat = Zero | Suc Nat

type role Vec nominal representational
data Vec :: Nat -> * -> * where
    Nil  :: Vec Zero a
    (:*) :: a -> Vec n a -> Vec (Suc n) a

vec1 :: Vec Zero Int
vec1 = Nil

vec2 :: Vec Zero Bool
vec2 = Nil

vec3 = 23 :* vec1
vec4 = True :* vec2

type role App representational nominal
data App (f :: k -> *) (a :: k) = App (f a)

type role Mu nominal nominal
data Mu (f :: (k -> *) -> k -> *) (a::k) = Roll (f (Mu f) a)

type role Proxy phantom
data Proxy (a::k) = Proxy



