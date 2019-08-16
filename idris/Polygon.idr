import Data.Vect

Position : Type
Position = (Double,Double)

-- hmmm...
Position' : (Type, Type)
Position' = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0,0),(3,0),(0,4)]
