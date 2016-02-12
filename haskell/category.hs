import Set

data Category arrow = Category { source   :: arrow -> arrow,
                                 target   :: arrow -> arrow,
                                 compose  :: arrow -> arrow -> arrow}



-- underlying class (set in this case) of the category 
-- of finite sets with elements of type a
data Arrow a = Arrow (Set a) (Set a) (a -> a)

setSource :: Arrow a -> Arrow a
setSource (Arrow x y f) = Arrow x x (\u -> u)

setTarget :: Arrow a -> Arrow a
setTarget (Arrow x y f) = Arrow y y (\u -> u)

setCompose :: (Eq a) => Arrow a -> Arrow a -> Arrow a
setCompose (Arrow x y f) (Arrow y' z g) = if (y == y') then 
  Arrow x z (\u ->  g (f u)) else error "Arrows are not composable"

finiteSet :: (Eq a) => Category (Arrow a)
finiteSet = Category setSource setTarget setCompose

