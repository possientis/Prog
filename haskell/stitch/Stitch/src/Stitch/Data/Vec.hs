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

data Vec :: Type -> Nat -> Type where
  VNil :: Vec a 'Zero
  (:>) :: a -> Vec a n -> Vec a ('Succ n)

infixr 5 :>

deriving instance Show a => Show (Vec a n)

(!!!) :: Vec a n -> Fin n -> a
(!!!) (x :> _)  FZ     = x
(!!!) (_ :> xs) (FS j) = xs !!! j 

_vec1 :: Vec Int ('Succ ('Succ ('Succ 'Zero)))
_vec1 = 2 :> 1 :> 0 :> VNil

_vec2 :: Vec Int ('Succ ('Succ ('Succ 'Zero)))
_vec2 = 5 :> 4 :> 3 :> VNil

_test2 :: Int
_test2 = _vec1 !!! FZ

_test1 :: Int
_test1 = _vec1 !!! (FS FZ)

_test0 :: Int
_test0 = _vec1 !!! (FS (FS FZ))

type family (v :: Vec a n) :!: (i :: Fin n) :: a where
  (x ':> _ ) :!:  'FZ     = x
  (_ ':> xs) :!: ('FS j)  = xs :!: j

elemIndex :: Eq a => a -> Vec a n -> Maybe (Fin n)
elemIndex _ VNil  = Nothing
elemIndex x (y :> ys)
  | x == y    = Just FZ
  | otherwise = FS <$> elemIndex x ys

(+++) :: Vec a n -> Vec a m -> Vec a (n :+: m)
(+++) VNil ys = ys
(+++) (x :> xs) ys = x :> (xs +++ ys)

type family (v1 :: Vec a n) :++: (v2 :: Vec a m) :: Vec a (n :+: m) where
  'VNil      :++: v2 = v2
  (x ':> xs) :++: v2 = x ':> (xs :++: v2)

data Length :: forall a n . Vec a n -> Type where
  LZ :: Length 'VNil
  LS :: Length xs -> Length (x ':> xs)

deriving instance Show (Length xs)

data Elem :: forall a n . Vec a n -> a -> Type where
  EZ :: Elem (x ':> xs) x
  ES :: Elem xs x -> Elem (y ':> xs) x

deriving instance Show (Elem xs x)

eqElem 
  :: forall (a :: Type) (n :: Nat) (xs :: Vec a n) (x1 :: a) (x2 :: a) 
   . Elem xs x1 
  -> Elem xs x2
  -> Maybe (x1 :~: x2)
eqElem  EZ      EZ     = Just Refl
eqElem (ES e1) (ES e2) = eqElem e1 e2
eqElem  _       _      = Nothing

elemToInt 
  :: forall (a :: Type) (n :: Nat) (xs :: Vec a n) (x :: a) 
   . Elem xs x 
  -> Int
elemToInt  EZ     = 0
elemToInt (ES e)  = 1 + elemToInt e

elemToFin 
  :: forall (a :: Type) (n :: Nat) (xs :: Vec a n) (x :: a)
   . Elem xs x 
  -> Fin n
elemToFin EZ      = FZ
elemToFin (ES e)  = FS (elemToFin e) 

weakenElem 
  :: forall 
      (a :: Type) (n :: Nat) (m :: Nat) 
      (prefix :: Vec a n) (xs :: Vec a m) (x :: a) 
   . Length prefix 
  -> Elem xs x 
  -> Elem (prefix :++: xs) x
weakenElem  LZ e      = e
weakenElem (LS len) e = ES (weakenElem len e)

strengthenElem 
  :: forall 
      (a :: Type) (n :: Nat) (m :: Nat)
      (prefix :: Vec a n) (xs :: Vec a m) (x :: a) 
   . Length prefix 
  -> Elem (prefix :++: xs) x 
  -> Maybe (Elem xs x)
strengthenElem  LZ e     = Just e
strengthenElem (LS _) EZ = Nothing
strengthenElem (LS len) (ES e) = strengthenElem len e
