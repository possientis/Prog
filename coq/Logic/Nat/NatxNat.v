Definition f1 (x y:nat) : nat * nat := (x + y, y).

Fixpoint f2 (n:nat) : nat := 
    match n with
    | 0     => 0
    | S n   => f2 n + S (S n)
    end.  

Definition f3 (x y:nat) : nat :=
    match x with
    | 0     => f2 y 
    | S x   => f2 x + S y
    end. 
(*
Compute f3 0 0.
Compute f3 1 0.
Compute f3 0 1.
Compute f3 2 0.
Compute f3 1 1.
Compute f3 0 2.
Compute f3 3 0.
Compute f3 2 1.
Compute f3 1 2.
Compute f3 0 3.
*)
