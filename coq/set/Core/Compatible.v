Require Import Core.Set.
Require Import Core.Equal.

Definition compatible (p:set -> Prop) : Prop :=
    forall (x x':set), x == x' -> p x -> p x'.

Definition compatible2 (p:set -> set -> Prop) : Prop :=
    forall (x x' y y':set), x == x' -> y == y' -> p x y -> p x' y'.

Lemma Comp2Comp : forall (p:set -> set -> Prop) (x:set),
    compatible2 p -> compatible (p x).
Proof.
    intros p x H. unfold compatible2 in H. unfold compatible.
    intros y y' Hy. apply H.
    - apply equalRefl.
    - assumption.
Qed.
