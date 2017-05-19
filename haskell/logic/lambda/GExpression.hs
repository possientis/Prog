module GExpression (GExpression) where

import LambdaCalculus

newtype GExpression v = GExpression (ExpressionType v GExpression)  -- fixed point


instance LambdaCalculus GExpression where
  variable x  = GExpression (VariableType x)
  apply p q   = GExpression (ApplyType p q)
  lambda x p  = GExpression (LambdaType x p)
  asType (GExpression t) = t

instance (Eq v) => Eq (GExpression v) where
  (==)  = equalF

instance (Show v) => Show (GExpression v) where
  show = showF

instance Functor GExpression where
  fmap = mapF
