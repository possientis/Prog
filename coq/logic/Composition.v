(* we are running out of operator symbols. Using ';' for composition in the *)
(* usual sense of '.', so 'g ; f' means f is applied first               *)

Definition comp (v w u:Type) (g:w -> u) (f:v -> w) (x:v) : u := g (f x).

Arguments comp {v} {w} {u} _ _ _.

Notation "g ; f" := (comp g f) 
    (at level 60, right associativity) : Composition.
