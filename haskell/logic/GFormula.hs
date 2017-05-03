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
  (==)  (GFormula (BelongType x1 y1))
        (GFormula (BelongType x2 y2))   = (x1 == x2) && (y1 == y2) 
  (==)  (GFormula (BotType))
        (GFormula (BotType))            = True
  (==)  (GFormula (ImplyType p1 q1))
        (GFormula (ImplyType p2 q2))    = (p1 == p2) && (q1 == q2)
  (==)  (GFormula (ForallType x1 p1))
        (GFormula (ForallType x2 p2))   = (x1 == x2) && (p1 == p2)

 
