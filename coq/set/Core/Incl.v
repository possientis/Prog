Require Import Le.
Require Import Plus.

Require Import Core.Set.
Require Import Core.Nat.
Require Import Core.Core.
Require Import Core.Order.

Definition incl (xs ys:set) : Prop :=
    let n := order xs + order ys in incl_n n xs ys.


Notation "x <== y" := (incl x y) (at level 90) : set_scope.

Open Scope set_scope.

Lemma incl_incl_n : forall (xs ys:set) (n:nat),
    order xs + order ys <= n    ->
    xs <== ys                   ->
    incl_n n xs ys.
Proof.
    intros xs ys n H1 H2. unfold incl in H2.
    apply incl_n_m with (order xs + order ys).
    - apply le_n.
    - assumption.
    - assumption.
Qed.

Lemma incl_n_incl : forall (xs ys:set) (n:nat),
    order xs + order ys <= n    ->
    incl_n n xs ys              ->
    xs <== ys.
Proof.
    intros xs ys n H1 H2. unfold incl.
    apply incl_n_m with n. 
    - assumption.
    - apply le_n.
    - assumption.
Qed.

Lemma inclNil : forall (x:set), Nil <== x.
Proof.
    intros x. unfold incl. apply incl_n_Nil. 
Qed.

Lemma incl_refl : forall (x:set), x <== x.
Proof.
    intros x. apply incl_n_incl with (order x + order x).
    - apply le_n.
    - apply incl_n_refl. apply le_plus_l.
Qed.



