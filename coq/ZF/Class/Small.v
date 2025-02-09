Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.

(* Predicate on classes, stating that a class is actually a set.                *)
Definition Small (P:Class) : Prop := exists a, forall x, x :< a <-> P x.

(* The class associated with a set is small.                                    *)
Proposition SetIsSmall : forall (a:U), Small (toClass a).
Proof.
  intros a. exists a. intro x. unfold toClass. split; auto.
Qed.

(* A class is small if and only if it is equivalent to some set.                *)
Proposition SmallIsSomeSet : forall (P:Class),
  Small P <-> exists a, toClass a :~: P.
Proof.
  intros P. split; intros [a H1]; exists a.
  - intros x. apply H1.
  - apply H1.
Qed.

(* The property of being small is compatible with class equivalence.            *)
Proposition SmallEquivCompat : forall (P Q:Class),
  P :~: Q -> Small P -> Small Q.
Proof.
  intros P Q H1 [a H2]. exists a. intros x. split; intros H3.
  - apply H1, H2, H3.
  - apply H2, H1, H3.
Qed.
