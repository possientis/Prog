Require Import Setoids.
Require Import Eq.

Definition Equalities (a:Type) : Setoid := setoid
    (Eq a)
    (eqEq a).




(*
Definition equalSet (x y:Setoid) : Prop :=
    (elems x = elems y)/\(equalEq (eqElems x) (eqElems y)).
*)




