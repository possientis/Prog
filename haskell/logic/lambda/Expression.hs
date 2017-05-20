module Expression 
  ( Expression(..)
  , variable
  , apply
  , lambda 
  ) where

data Expression v
  = Variable v
  | Apply (Expression v) (Expression v)
  | Lambda v (Expression v)
  deriving (Eq)

variable  = Variable
apply     = Apply
lambda    = Lambda 

fold :: (v -> b) -> (b -> b -> b) -> (v -> b -> b) -> Expression v -> b
fold fvar fapply flambda = f where
  f (Variable x)  = fvar x
  f (Apply p q)   = fapply (f p) (f q)
  f (Lambda x p)  = flambda x (f p)

instance (Show v) => Show (Expression v) where
  show  = fold fvar fapply flambda where
    fvar x      = (show x)
    fapply s t  = "(" ++ s ++ " " ++ t ++ ")"
    flambda x s = "L" ++ (show x) ++ "." ++ s

instance Functor Expression where
  fmap f  = fold fvar fapply flambda where
    fvar x      = variable (f x)
    fapply p q  = apply p q 
    flambda x p = lambda (f x) p
