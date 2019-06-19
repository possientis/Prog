Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Fol.P.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a lambda abstraction, we need to be able to remove a variable    *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint free (v:Type) (e:Eq v) (p:P v) : list v :=
    match p with
    | Bot           => [ ]
    | Elem x y      => [x;y]
    | Imp p1 p2     => free v e p1 ++ free v e p2
    | All x p1      => remove e x (free v e p1)
    end.

Arguments free {v} _ _.
