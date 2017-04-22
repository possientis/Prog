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

instance (FirstOrder m) => Functor m where
  fmap f (asType -> BelongType x y)  = belong (f x) (f y)
  fmap f (asType -> BotType)         = bot
  fmap f (asType -> ImplyType p q)   = imply (fmap f p) (fmap f q)  
  fmap f (asType -> ForallType x p)  = forall (f x) (fmap f p)

data FormulaType v k  = BelongType v v 
                      | BotType
                      | ImplyType (k v) (k v)
                      | ForallType v (k v)





