Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Image.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Core.Inverse.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Inverse image of P by F is the direct image of P by F^(-1).                  *)
Proposition InvImageCharac : forall (F:Class) (P:Class) (x:U),
  F^:-1: :[P]: x <-> exists y, P y /\ F :(x,y):.
Proof.
  intros F P x. split; intros H1.
  - apply (proj1 (ImageCharac _ _ _)) in H1. destruct H1 as [y [H1 H2]].
    apply (proj1 (ConverseCharac2 _ _ _)) in H2.
    exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply ImageCharac. exists y. split.
    + assumption.
    + apply ConverseCharac2. assumption.
Qed.

(* The inverse image is compatible with equivalences.                           *)
Proposition InvImageEquivCompat : forall (F G:Class) (P Q:Class),
  F :~: G -> P :~: Q -> F^:-1: :[P]: :~: G^:-1: :[Q]:.
Proof.
  intros F G P Q H1 H2. apply ImageEquivCompat. 2: assumption.
  apply ConverseEquivCompat. assumption.
Qed.

(* The inverse image is left-compatible with equivalences.                      *)
Proposition InvImageEquivCompatL : forall (F G:Class) (P:Class),
  F :~: G -> F^:-1: :[P]: :~: G^:-1: :[P]:.
Proof.
  intros F G P H1. apply InvImageEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

(* The inverse image is right-compatible with equivalences.                     *)
Proposition ImageEquivCompatR : forall (F:Class) (P Q:Class),
  P :~: Q -> F^:-1: :[P]: :~: F^:-1: :[Q]:.
Proof.
  intros F P Q H1. apply InvImageEquivCompat.
  - apply ClassEquivRefl.
  - assumption.
Qed.
