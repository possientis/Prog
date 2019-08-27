Require Import List.
Import ListNotations.

Require Import Eq.

Fixpoint diff (v:Type) (e:Eq v) (xs ys:list v) : list v :=
    match xs with
    | []        => []
    | (x :: xs) =>
        match in_dec e x ys with
        | left  _   => diff v e xs ys
        | right _   => x :: diff v e xs ys
        end
    end.
