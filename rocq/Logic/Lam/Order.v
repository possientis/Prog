Require Import Logic.Lam.Syntax.

Fixpoint ord (v:Type) (t:T v) : nat :=
    match t with
    | Var x     => 0
    | App t1 t2 => S (max (ord v t1) (ord v t2))
    | Lam x t1  => S (ord v t1)
    end.

Arguments ord {v} _.


