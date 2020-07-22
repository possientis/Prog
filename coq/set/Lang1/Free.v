Require Import List.
Require Import Peano_dec.

Require Import Lang1.Syntax.


(* Free variables of a formula.                                                 *)
Fixpoint free (p:Formula) : list nat :=
    match p with
    | Bot       => nil
    | Elem n m  => cons n (cons m nil)
    | Imp p q   => free p ++ free q
    | All n p   => remove (eq_nat_dec) n (free p)
    end.  


