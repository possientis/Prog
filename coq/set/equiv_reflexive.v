Set Implicit Arguments.

Require Import set.
Require Import equiv.
Require Import subset_reflexive.

Lemma equiv_reflexive: forall (a:set), equiv a a.
Proof.
  intro a. unfold equiv. simpl. split. apply subset_reflexive.
  apply subset_reflexive.
Qed.


