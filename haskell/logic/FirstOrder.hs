{-# LANGUAGE ViewPatterns, FlexibleInstances, UndecidableInstances #-}

module FirstOrder
  ( FirstOrder
  , FormulaType(BelongType, BotType, ImplyType, ForallType)
  , belong
  , bot
  , imply
  , forall
  , asType
  ) where

class FirstOrder m where
  belong    :: v -> v -> m v
  bot       :: m v
  imply     :: m v -> m v -> m v
  forall    :: v -> m v -> m v
  asType    :: m v -> FormulaType v m 

data  FormulaType v k  
    = BelongType v v 
    | BotType
    | ImplyType (k v) (k v)
    | ForallType v (k v)

instance (Eq v, FirstOrder m) => Eq (m v) where
  (==)  (asType -> BelongType x1 y1) 
        (asType -> BelongType x2 y2)  = (x1 == x2) && (y1 == y2)
  (==)  (asType -> BotType)
        (asType -> BotType)           = True
  (==)  (asType -> ImplyType p1 q1) 
        (asType -> ImplyType p2 q2)   = (p1 == p2) && (q1 == q2) 
  (==)  (asType -> ForallType x1 p1)
        (asType -> ForallType x2 p2)  = (x1 == x2) && (p1 == p2)
  (==)  _ 
        _                             = False

instance (Show v, FirstOrder m) => Show (m v) where
  show (asType -> BelongType x y) = (show x) ++ ":" ++ (show y)
  show (asType -> BotType)        = "!"
  show (asType -> ImplyType p q)  = "(" ++ (show p) ++ " -> " ++ (show q) ++ ")"
  show (asType -> ForallType x p) = "A" ++ (show x) ++ "." ++ (show p)
  

instance (FirstOrder m) => Functor m where
  fmap f (asType -> BelongType x y)  = belong (f x) (f y)
  fmap f (asType -> BotType)         = bot
  fmap f (asType -> ImplyType p q)   = imply (fmap f p) (fmap f q)  
  fmap f (asType -> ForallType x p)  = forall (f x) (fmap f p)





