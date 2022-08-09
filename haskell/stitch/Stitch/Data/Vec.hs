{-# LANGUAGE ExplicitForAll     #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}

module Stitch.Data.Vec 
  ( Elem    (..)
  , Length  (..)
  , Vec     (..)
  , (!!!)
  , (:!:)
  , (+++)
  , (:++:)
  , elemIndex
  , elemToFin
  , elemToInt
  , eqElem
  , strengthenElem
  , weakenElem
  ) where

import Data.Kind
import Data.Type.Equality

import Stitch.Data.Fin
import Stitch.Data.Nat

data Vec :: Nat -> Type -> Type where
  VNil :: Vec 'Zero a
  (:>) :: a -> Vec n a -> Vec ('Succ n) a

infixr 5 :>

deriving instance Show a => Show (Vec n a)

(!!!) :: Vec n a -> Fin n -> a
(!!!) (x :> _)  FZ     = x
(!!!) (_ :> xs) (FS j) = xs !!! j 

_vec1 :: Vec ('Succ ('Succ ('Succ 'Zero))) Int
_vec1 = 2 :> 1 :> 0 :> VNil

_vec2 :: Vec ('Succ ('Succ ('Succ 'Zero))) Int
_vec2 = 5 :> 4 :> 3 :> VNil

_test2 :: Int
_test2 = _vec1 !!! FZ

_test1 :: Int
_test1 = _vec1 !!! (FS FZ)

_test0 :: Int
_test0 = _vec1 !!! (FS (FS FZ))

type family (v :: Vec n a) :!: (i :: Fin n) :: a where
  (x ':> _ ) :!:  'FZ     = x
  (_ ':> xs) :!: ('FS j)  = xs :!: j

elemIndex :: Eq a => a -> Vec n a -> Maybe (Fin n)
elemIndex _ VNil  = Nothing
elemIndex x (y :> ys)
  | x == y    = Just FZ
  | otherwise = FS <$> elemIndex x ys

(+++) :: Vec n a -> Vec m a -> Vec (n :+: m) a
(+++) VNil ys = ys
(+++) (x :> xs) ys = x :> (xs +++ ys)

type family (v1 :: Vec n a) :++: (v2 :: Vec m a) :: Vec (n :+: m) a where
  'VNil      :++: v2 = v2
  (x ':> xs) :++: v2 = x ':> (xs :++: v2)

data Length :: forall a n . Vec n a -> Type where
  LZ :: Length 'VNil
  LS :: Length xs -> Length (x ':> xs)

deriving instance Show (Length xs)

data Elem :: forall a n . a -> Vec n a -> Type where
  EZ :: Elem x (x ':> xs)
  ES :: Elem x xs -> Elem x (y ':> xs)

eqElem :: Elem x1 xs -> Elem x2 xs -> Maybe (x1 :~: x2)
eqElem  EZ      EZ     = Just Refl
eqElem (ES e1) (ES e2) = eqElem e1 e2
eqElem  _       _      = Nothing

elemToInt :: Elem ty ctx -> Int
elemToInt  EZ     = 0
elemToInt (ES e)  = 1 + elemToInt e

elemToFin :: Elem x (ctx :: Vec n a) -> Fin n
elemToFin EZ      = FZ
elemToFin (ES e)  = FS (elemToFin e) 

weakenElem :: Length prefix -> Elem x xs -> Elem x (prefix :++: xs)
weakenElem  LZ      e = e
weakenElem (LS len) e = ES (weakenElem len e)

strengthenElem :: Length prefix -> Elem x (prefix :++: xs) -> Maybe (Elem x xs)
strengthenElem  LZ e     = Just e
strengthenElem (LS _) EZ = Nothing
strengthenElem (LS len) (ES e) = strengthenElem len e
