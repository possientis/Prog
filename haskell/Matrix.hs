{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}

import Prelude      hiding (zipWith)
import Data.Kind

data Nat = Z | S Nat

data Vect (n :: Nat) (a :: Type) :: Type where
    Nil  :: Vect 'Z a
    (:>) :: a -> Vect n a -> Vect ('S n) a 

infixr 4 :>

instance Functor (Vect n) where 
    fmap _ Nil       = Nil
    fmap f (x :> xs) = f x :> fmap f xs 

toList :: Vect n a -> [a]
toList Nil       = []
toList (x :> xs) = x : toList xs

instance (Show a) =>  Show (Vect n a) where
    show = show . toList

zipWith :: (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith _ Nil Nil = Nil
zipWith f (x :> xs) (y :> ys) = f x y :> zipWith f xs ys


transMatrix :: (CreateEmpties m) => Vect n (Vect m a) -> Vect m (Vect n a)
transMatrix Nil       = createEmpties
transMatrix (x :> xs) = zipWith (:>) x (transMatrix xs)

dot :: (Num a) => Vect n a -> Vect n a -> a
dot Nil Nil = 0
dot (x :> xs) (y :> ys) = (x * y) + dot xs ys

mulMatrix :: (Num a, CreateEmpties p)
    => Vect n (Vect m a)
    -> Vect m (Vect p a)
    -> Vect n (Vect p a)
mulMatrix xs ys = 
    let zs = transMatrix ys in
        fmap (\v -> fmap (dot v) zs) xs

class CreateEmpties (n :: Nat) where
    createEmpties :: Vect n (Vect 'Z a) 
    
instance CreateEmpties 'Z where
    createEmpties = Nil

instance (CreateEmpties n) => CreateEmpties ('S n) where
    createEmpties = Nil :> createEmpties

type Two   = 'S ('S 'Z)
type Three = 'S Two
type Four  = 'S Three

a1 :: Vect Two Int
a1 = 1 :> 2 :> Nil

a2 :: Vect Two Int
a2 = 3 :> 4 :> Nil

a3 :: Vect Two Int
a3 = 5 :> 6 :> Nil

a :: Vect Three (Vect Two Int)
a = a1 :> a2 :> a3 :> Nil

b1 :: Vect Four Int
b1 = 7 :> 8 :> 9 :> 10 :> Nil

b2 :: Vect Four Int
b2 = 11 :> 12 :> 13 :> 14 :> Nil

b :: Vect Two (Vect Four Int)
b = b1 :> b2 :> Nil

main :: IO()
main = do
    print $ mulMatrix a b



