{-# LANGUAGE ViewPatterns #-}

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
  fold      :: (v -> v -> b) -> b -> (b -> b -> b) -> (v -> b -> b) -> m v -> b
  fold  fbelong fbot fimply fforall = f where
    f (asType -> BelongType x y)  = fbelong x y
    f (asType -> BotType)         = fbot
    f (asType -> ImplyType p q)   = fimply (f p) (f q)
    f (asType -> ForallType x p)  = fforall x (f p)

  equalF :: (Eq v) => m v -> m v -> Bool
  equalF (asType -> BelongType x1 y1)
         (asType -> BelongType x2 y2) = (x1 == x2) && (y1 == y2)
  equalF (asType -> BotType)
         (asType -> BotType)          = True
  equalF (asType -> ImplyType p1 q1)
         (asType -> ImplyType p2 q2)  = (equalF p1 p2) && (equalF q1 q2)
  equalF (asType -> ForallType x1 p1)
         (asType -> ForallType x2 p2) = (x1 == x2) && (equalF p1 p2)
  equalF  _ _                         = False

  showF :: (Show v) => m v -> String
  showF = fold fbelong fbot fimply fforall where
    fbelong x y = (show x) ++ ":" ++ (show y)
    fbot        = "!"
    fimply s t  = "(" ++ s ++ " -> " ++ t ++ ")"
    fforall x s = "A" ++ (show x) ++ "." ++ s

  mapF  :: (v -> w) -> m v -> m w
  mapF f  = fold fbelong fbot fimply fforall where
    fbelong x y = belong (f x) (f y)
    fbot        = bot
    fimply p q  = imply p q
    fforall x p = forall (f x) p
        

