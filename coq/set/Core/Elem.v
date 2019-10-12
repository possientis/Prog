Require Import List.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Core.
Require Import Core.Order.
Require Import Core.ToList.

Notation "{ x }" := (Cons x Nil) : set_scope.

Open Scope set_scope.

Definition elem (x y:set) : Prop := incl {x} y. 

Notation "x :: y" := (elem x y) : set_scope.


(*
Lemma elem_incl : forall (x y:set), 
    x <== y <-> forall (z:set), z :: x -> z :: y.
Proof.
    intros x y. split; intros H.
    - intros z H'. unfold elem. unfold incl. simpl. split.
        + simpl. apply incl_n_Nil.
        +

Show.
*)
