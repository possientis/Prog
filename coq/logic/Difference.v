Require Import List.
Import ListNotations.

Require Import Eq.

Fixpoint diff (v:Type) (e:Eq v) (xs ys:list v) : list v :=
    match ys with
    | []        => xs
    | (y :: ys) => remove e y (diff v e xs ys)
    end.
