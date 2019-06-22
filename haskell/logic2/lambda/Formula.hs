module Formula 
  ( Formula(..)
  , variable
  , apply
  , lambda 
  ) where

data Formula v
  = Variable v
  | Apply (Formula v) (Formula v)
  | Lambda v (Formula v)
  deriving (Eq, Ord)

variable  = Variable
apply     = Apply
lambda    = Lambda 

fold :: (v -> b) -> (b -> b -> b) -> (v -> b -> b) -> Formula v -> b
fold fvar fapply flambda = f where
  f (Variable x)  = fvar x
  f (Apply p q)   = fapply (f p) (f q)
  f (Lambda x p)  = flambda x (f p)

instance (Show v) => Show (Formula v) where
  show  = fold fvar fapply flambda where
    fvar x      = (show x)
    fapply s t  = "(" ++ s ++ " " ++ t ++ ")"
    flambda x s = "L" ++ (show x) ++ "." ++ s

instance Functor Formula where
  fmap f  = fold fvar fapply flambda where
    fvar x      = variable (f x)
    fapply p q  = apply p q 
    flambda x p = lambda (f x) p
