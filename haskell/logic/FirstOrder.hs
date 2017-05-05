{-# LANGUAGE ViewPatterns, FlexibleInstances, UndecidableInstances #-}

module FirstOrder
  ( FirstOrder
  , FormulaType(BelongType, BotType, ImplyType, ForallType)
  , belong
  , bot
  , imply
  , forall
  , asType
  , equalF
  , showF
  , mapF
  ) where

data  FormulaType v k  
    = BelongType v v 
    | BotType
    | ImplyType (k v) (k v)
    | ForallType v (k v)


class FirstOrder m where
  belong    :: v -> v -> m v
  bot       :: m v
  imply     :: m v -> m v -> m v
  forall    :: v -> m v -> m v
  asType    :: m v -> FormulaType v m 

  equalF :: (Eq v) => m v -> m v -> Bool
  equalF (asType -> BelongType x1 y1)
         (asType -> BelongType x2 y2)  = (x1 == x2) && (y1 == y2)
  equalF (asType -> BotType)
         (asType -> BotType)           = True
  equalF (asType -> ImplyType p1 q1)
         (asType -> ImplyType p2 q2)   = (equalF p1 p2) && (equalF q1 q2)
  equalF (asType -> ForallType x1 p1)
         (asType -> ForallType x2 p2)  = (x1 == x2) && (equalF p1 p2)
  equalF  _ _                          = False

  showF :: (Show v) => m v -> String
  showF (asType -> BelongType x y)  = (show x) ++ ":" ++ (show y)
  showF (asType -> BotType)         = "!"
  showF (asType -> ImplyType p q)   = "(" ++ (showF p) ++ " -> " ++ (showF q) ++ ")"
  showF (asType -> ForallType x p)  = "A" ++ (show x) ++ "." ++ (showF p) 

  mapF  :: (v -> w) -> m v -> m w
  mapF  f (asType -> BelongType x y)   = belong (f x) (f y)
  mapF  f (asType -> BotType)          = bot
  mapF  f (asType -> ImplyType p q)    = imply (mapF f p) (mapF f q)
  mapF  f (asType -> ForallType x p)   = forall (f x) (mapF f p)
        





