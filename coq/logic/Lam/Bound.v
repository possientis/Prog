Require Import List.
Import ListNotations.

Require Import Lam.T.

Fixpoint bnd (v:Type) (t:T v) : list v :=
    match t with
    | Var x     => []
    | App t1 t2 => bnd v t1 ++ bnd v t2
    | Lam x t1  => x :: bnd v t1
    end.


Arguments bnd {v} _.
