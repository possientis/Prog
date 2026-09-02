Declare Scope composition.

Definition comp (v w u:Type) (g:w -> u) (f:v -> w) (x:v) : u := g (f x).

Arguments comp {v} {w} {u} _ _ _.

Notation "g ; f" := (comp g f) (at level 60, right associativity) : composition.
