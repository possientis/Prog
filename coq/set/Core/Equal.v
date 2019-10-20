Require Import Core.Set.
Require Import Core.Elem.

Open Scope set_scope.

Definition equal (x y:set) : Prop :=
    (forall (z:set), z :: x <-> z :: y) 
 /\ (forall (z:set), x :: z <-> y :: z). 

Notation "x == y" := (equal x y) (at level 90) : set_scope.

Lemma equal_refl : forall (x:set), x == x.
Proof.
    intros x. split; intros z; split; intros H; assumption.
Qed.

Lemma equal_sym : forall (x y:set), x == y -> y == x.
Proof.
    intros x y [H1 H2]. split; intros z; split; intros H.
    - apply H1. assumption.
    - apply H1. assumption.
    - apply H2. assumption.
    - apply H2. assumption.
Qed.

Lemma equal_trans : forall (x y z:set), x == y -> y == z -> x == z.
Proof.
    intros x y z [H1 H2] [H3 H4]. split; intro t; split; intros H.
    - apply H3, H1. assumption.
    - apply H1, H3. assumption.
    - apply H4, H2. assumption.
    - apply H2, H4. assumption.
Qed.

