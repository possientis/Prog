module  Formula (Formula) where

import FirstOrder

data Formula v  
  = Belong v v
  | Bot
  | Imply (Formula v) (Formula v)
  | Forall v (Formula v)

instance FirstOrder Formula where
  belong  = Belong
  bot     = Bot  
  imply   = Imply
  forall  = Forall
  asType  (Belong x y)  = BelongType x y
  asType  (Bot)         = BotType
  asType  (Imply p q)   = ImplyType p q
  asType  (Forall x p)  = ForallType x p 

instance (Eq v) => Eq (Formula v) where
  (==) = equalF

instance (Show v) => Show (Formula v) where
  show = showF

instance Functor Formula where
  fmap f (Belong x y)   = Belong (f x) (f y)
  fmap f (Bot)          = Bot
  fmap f (Imply p q)    = Imply (fmap f p) (fmap f q)
  fmap f (Forall x p)   = Forall (f x) (fmap f p)

