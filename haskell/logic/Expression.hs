module Expression (Expression) where

import LambdaCalculus

data Expression v
  = Variable v
  | Apply (Expression v) (Expression v)
  | Lambda v (Expression v)


instance LambdaCalculus Expression where
  variable  = Variable
  apply     = Apply
  lambda    = Lambda
  asType    (Variable x)  = VariableType x
  asType    (Apply p q)   = ApplyType p q
  asType    (Lambda x p)  = LambdaType x p

instance (Eq v) => Eq (Expression v) where
  (==)  = equalF 

instance (Show v) => Show (Expression v) where
  show  = showF

instance Functor Expression where
  fmap = mapF
