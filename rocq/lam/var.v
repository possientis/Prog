Require Import List.
Import ListNotations.

Require Import term.


Fixpoint Vr (v:Type) (t:P v) : list v :=
    match t with
    | Var x         => [x]
    | App t1 t2     => Vr v t1 ++ Vr v t2
    | Lam x t1      => x :: Vr v t1
    end.


Arguments Vr {v} _.
