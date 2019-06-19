Require Import List.
Import ListNotations.

Require Import Eq.
Require Import Lam.T.

(* Returns the list of free variables (with possible duplication) in a term     *)
(* When facing a lambda abstraction, we need to be able to remove a variable    *)
(* from the list of free variables of the subterm, hence decidable equality.    *)
Fixpoint free (v:Type) (e:Eq v) (t:T v) : list v :=
    match t with
    | Var x         => [x]
    | App t1 t2     => free v e t1 ++ free v e t2
    | Lam x t1      => remove e x (free v e t1)
    end.

Arguments free {v} _ _.



