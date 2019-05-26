Require Import Fol.P.

(* We do not have sets: the variables of a formula are a list, not a set.       *)

Fixpoint var (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => nil
    | Elem x y  => cons x (cons y nil)
    | Imp p1 p2 => var v p1 ++ var v p2
    | All x p1  => cons x (var v p1)
    end.

Arguments var {v} _.
