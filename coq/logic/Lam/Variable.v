Require Import Lam.T.

(* We do not have sets: the variables of a term are a list, not a set.          *)

Fixpoint var (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => cons x nil
    | App t1 t2 => var v t1 ++ var v t2
    | Lam x t1  => cons x  (var v t1)
    end.

Arguments var {v} _.
