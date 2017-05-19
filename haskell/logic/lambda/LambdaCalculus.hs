{-# LANGUAGE ViewPatterns #-}

module LambdaCalculus
  ( LambdaCalculus
  , ExpressionType (VariableType, ApplyType, LambdaType)
  , variable
  , apply
  , lambda
  , asType
  , equalF
  , showF
  , mapF
  ) where

data  ExpressionType v k
  = VariableType v
  | ApplyType (k v) (k v)
  | LambdaType v (k v)


class LambdaCalculus m where
  variable :: v -> m v
  apply    :: m v -> m v -> m v
  lambda   :: v -> m v -> m v
  asType   :: m v -> ExpressionType v m
  fold     :: (v -> b) -> (b -> b -> b) -> (v -> b -> b) -> m v -> b
  fold fvariable fapply flambda = f where
    f (asType -> VariableType x) = fvariable x
    f (asType -> ApplyType p q)  = fapply (f p) (f q)
    f (asType -> LambdaType x p) = flambda x (f p)


  equalF :: (Eq v) => m v -> m v -> Bool
  equalF  (asType -> VariableType x) 
          (asType -> VariableType y)    = (x == y)
  equalF  (asType -> ApplyType p1 q1) 
          (asType -> ApplyType p2 q2)   = (equalF p1 p2) && (equalF q1 q2) 
  equalF  (asType -> LambdaType x1 p1)
          (asType -> LambdaType x2 p2)  = (x1 == x2) && (equalF p1 p2)
  equalF  _ _                           = False

  showF :: (Show v) => m v -> String
  showF = fold fvariable fapply flambda where
    fvariable x = (show x)
    fapply s t  = "(" ++ s ++ " " ++ t ++ ")"
    flambda x s = "L" ++ (show x) ++ "." ++ s

  mapF  :: (v -> w) -> m v -> m w
  mapF f  = fold fvariable fapply flambda where
    fvariable x = variable (f x)
    fapply p q  = apply p q
    flambda x p = lambda (f x) p




