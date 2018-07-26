(* In practice, not much can be done without decidable equality *)
(* Many functions require an argument p of type Eq v            *) 

Definition Eq (v:Type) := forall (x y:v), {x = y} + {x <> y}.
