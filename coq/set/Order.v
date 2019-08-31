Require Import Arith.Max.

Require Import set.

Fixpoint order (xs:set) : nat :=
    match xs with
    | Nil       =>  0
    | Cons x xs =>  1 + max (order x) (order xs)
    end.



