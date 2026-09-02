Require Import Logic.Set.Set.
Require Import Logic.Set.Equal.

Definition compatible (p:set -> Prop) : Prop :=
    forall (x x':set), x == x' -> p x -> p x'.

Definition compatible2 (p:set -> set -> Prop) : Prop :=
    forall (x x' y y':set), x == x' -> y == y' -> p x y -> p x' y'.

Definition compatible3 (p:set -> set -> set -> Prop) : Prop :=
    forall (x x' y y' z z':set), 
        x == x' -> y == y' -> z == z' -> p x y z -> p x' y' z'.

Lemma Comp2Comp : forall (p:set -> set -> Prop) (x:set),
    compatible2 p -> compatible (p x).
Proof.
    intros p x H. unfold compatible2 in H. unfold compatible.
    intros y y' Hy. apply H.
    - apply equalRefl.
    - assumption.
Qed.

Lemma Comp3Comp2 : forall (p:set -> set -> set -> Prop) (x:set),
    compatible3 p -> compatible2 (p x).
Proof.
    intros p x H. unfold compatible3 in H. unfold compatible2.
    intros y y' z z' Hy Hz. apply H.
    - apply equalRefl.
    - assumption.
    - assumption.
Qed.


Lemma Comp3Comp : forall (p:set -> set -> set -> Prop) (x y:set),
    compatible3 p -> compatible (p x y).
Proof.
    intros p x y H. apply Comp2Comp. apply Comp3Comp2. assumption.
Qed.
