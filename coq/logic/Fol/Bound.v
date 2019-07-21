Require Import List.
Import ListNotations.

Require Import Fol.P.


Fixpoint bnd (v:Type) (p:P v) : list v :=
    match p with
    | Bot       => []
    | Elem x y  => []
    | Imp p1 p2 => bnd v p1 ++ bnd v p2
    | All x p1  => x :: bnd v p1
    end.


Arguments bnd {v} _.
