Require Import Fol.P.

Fixpoint ord (v:Type) (p:P v) : nat :=
    match p with
    | Bot       => 1 
    | Elem x y  => 0
    | Imp p1 p2 => S (max (ord v p1) (ord v p2))
    | All x p1  => S (ord v p1)
    end.

Arguments ord {v} _.
