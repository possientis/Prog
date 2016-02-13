import Set

-- underlying class (set in this case) of the category 
-- of finite sets with elements of type a
class Categorizable a where
  source :: a -> a
  target :: a -> a
  compose:: a -> a -> a
 

data FiniteSetArrow a = FSArrow (Set a) (Set a) (a -> a)
instance (Eq a) => Categorizable (FiniteSetArrow a) where
  source   (FSArrow x y f) = FSArrow x x (\u -> u)
  target   (FSArrow x y f) = FSArrow y y (\u -> u)
  compose  (FSArrow x y f) (FSArrow y' z g) = if (y == y') then 
    FSArrow x z (g.f) else error "FSArrows are not composable"


data PosetArrow a = PSArrow a a
instance (Ord a) => Categorizable (PosetArrow a) where
  source (PSArrow x y) = if x <= y then PSArrow x x else error "Illegal arrow"
  target (PSArrow x y) = if x <= y then PSArrow y y else error "Illegal arrow"
  compose(PSArrow x y) (PSArrow y' z) = 
    if x <= y && y' <= z then
      if y == y then
        PSArrow x z
      else
        error "Poset arrows are not composable"
    else
      error "Illegal poset arrow arguments"







