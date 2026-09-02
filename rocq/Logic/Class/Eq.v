Class Eq (v:Type) := { eqDec : forall (x y:v), {x = y} + {x <> y} }.
