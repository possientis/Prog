Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Set.

(* Inverse image of P by F is the direct image of P by F^(-1).                  *)
Proposition InvImageCharac : forall (F:Binary) (P:Class) (x:U),
  F^:-1: :[P]: x <-> exists y, P y /\ F x y.
Proof.
  intros F P x. split; intros H1.
  - apply (proj1 (ImageCharac _ _ _)) in H1. destruct H1 as [y [H1 H2]].
    exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply ImageCharac. exists y. split; assumption.
Qed.

(* The inverse image is compatible with equivalences.                           *)
Proposition InvImageEquivCompat : forall (F G:Binary) (P Q:Class),
  F :~: G -> P :~: Q -> F^:-1: :[P]: :~: G^:-1: :[Q]:.
Proof.
  intros F G P Q H1 H2. apply ImageEquivCompat. 2: assumption.
  apply ConverseEquivCompat. assumption.
Qed.

(* The inverse image is left-compatible with equivalences.                      *)
Proposition InvImageEquivCompatL : forall (F G:Binary) (P:Class),
  F :~: G -> F^:-1: :[P]: :~: G^:-1: :[P]:.
Proof.
  intros F G P H1. apply InvImageEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

(* The inverse image is right-compatible with equivalences.                     *)
Proposition ImageEquivCompatR : forall (F:Binary) (P Q:Class),
  P :~: Q -> F^:-1: :[P]: :~: F^:-1: :[Q]:.
Proof.
  intros F P Q H1. apply InvImageEquivCompat.
  - apply BinaryEquivRefl.
  - assumption.
Qed.
