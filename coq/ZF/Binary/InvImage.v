Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Set.

(* Inverse image of a class P by a binary class F.                              *)
Definition invImage (F:Binary) (P:Class) : Class := fun x =>
  exists y, P y /\ F x y.

(* The inverse image of P by F is the direct image of P by the converse of F.   *)
Proposition InvImageIsImageOfConverse : forall (F:Binary) (P:Class),
  invImage F P :~: (converse F) :[P]:.
Proof.
  intros F P x. split; intros H1.
  - destruct H1 as [y [H1 H2]]. apply ImageCharac. exists y. split; assumption.
  - apply (proj1 (ImageCharac _ _ _)) in H1. destruct H1 as [y [H1 H2]].
    exists y. split; assumption.
Qed.
