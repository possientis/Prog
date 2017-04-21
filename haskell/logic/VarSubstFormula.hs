{-# LANGUAGE ViewPatterns #-}

import Formula

gsubst :: (FirstOrder m) => (v -> w) -> m v -> m w
gsubst f p = 
  case toFormula p of
    Belong x y    -> belong (f x) (f y)
    Bot           -> bot
    Imply q q'    -> imply (gsubst f (fromFormula q)) (gsubst f (fromFormula q'))
    Forall x q    -> forall (f x) (gsubst f (fromFormula q))

subst :: (v -> w) -> Formula v -> Formula w
subst f (Belong x y) = belong (f x) (f y)
subst f  Bot         = bot
subst f (Imply p q)  = imply (subst f p) (subst f q)
subst f (Forall x p) = forall (f x) (subst f p)
          
