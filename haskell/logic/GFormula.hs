module GFormula (GFormula) where

import FirstOrder

newtype GFormula v = GFormula (FormulaType v GFormula) -- fixed point

instance FirstOrder GFormula where
  belong x y  = GFormula (BelongType x y)
  bot         = GFormula (BotType)
  imply  p q  = GFormula (ImplyType p q) 
  forall x p  = GFormula (ForallType x p)
  asType (GFormula t) = t


instance (Eq v) => Eq (GFormula v) where
  (==) = equalF
  
instance (Show v) => Show (GFormula v) where
  show = showF

instance Functor GFormula where
  fmap = mapF

 
