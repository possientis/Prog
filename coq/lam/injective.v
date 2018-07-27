Definition injective (v w:Type) (f:v -> w) : Prop :=
    forall (x y:v), f x = f y -> x = y.


Arguments injective {v} {w} _.


